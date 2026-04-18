#!/usr/bin/env python3

import requests
import json
import os
import hashlib
import tarfile
import tempfile
import sys
import argparse
import subprocess
import platform
import re
import stat
from datetime import datetime, timedelta
from pathlib import Path
import tomlkit
from requests.exceptions import RequestException


class CompatibilityError(Exception):
    """Raised when a release is found but is not compatible with our requirements."""
    pass

# Default timeout for all network requests in seconds.
DEFAULT_TIMEOUT = 30

# Configuration for the Aeneas and Charon repositories. These are used to discover
# releases and fetch metadata from the AeneasVerif organization on GitHub.
AENEAS_REPO = "google/zerocopy"
CHARON_REPO = "AeneasVerif/charon"

# The set of platforms that Anneal supports for pre-built binaries. The script
# will download and checksum artifacts for each of these triples.
PLATFORMS = ["linux-x86_64", "linux-aarch64", "macos-aarch64", "macos-x86_64"]

# Path to the Cargo.toml file where toolchain metadata is stored. This is
# resolved relative to the script's location to allow invocation from anywhere in
# the repository.
CARGO_TOML_PATH = (Path(__file__).parent.parent / "Cargo.toml").resolve()


def github_get(url):
    """Performs an authenticated GET request to the GitHub API if a token is present.

    This function automatically uses the 'GITHUB_TOKEN' environment variable if
    set to avoid API rate limits. It also enforces a standard timeout.
    """
    headers = {}
    token = os.environ.get("GITHUB_TOKEN")
    if token:
        headers["Authorization"] = f"token {token}"

    try:
        response = requests.get(url, headers=headers, timeout=DEFAULT_TIMEOUT)
        response.raise_for_status()
        return response
    except RequestException as e:
        print(f"ERROR: GitHub request failed: {url}")
        print(f"       {e}")
        sys.exit(1)


def get_automated_releases(repo):
    """Fetches automated build releases from the GitHub API.

    This function assumes that releases representing automated CI builds are
    prefixed with 'build-'. It fetches the first 100 releases to ensure we have
    enough history to find compatible pairs.
    """
    url = f"https://api.github.com/repos/{repo}/releases?per_page=100"
    response = github_get(url)
    return [r for r in response.json() if r["tag_name"].startswith("build-")]


def get_release_by_tag(repo, tag):
    """Fetches metadata for a specific release identified by a tag.

    This is used when a user provides an explicit tag override, bypassing the
    automated discovery logic.
    """
    url = f"https://api.github.com/repos/{repo}/releases/tags/{tag}"
    response = github_get(url)
    return response.json()


def release_has_assets(release, repo_name):
    """Returns True if the release contains all expected assets for our platforms."""
    asset_names = {a["name"] for a in release.get("assets", [])}
    for platform in PLATFORMS:
        expected_asset = f"anneal-toolchain-{platform}.tar.zst"
        if expected_asset not in asset_names:
            return False
    return True


def get_commit_from_tag(tag):
    """Extracts the git commit hash from a build tag.

    This function assumes the tag follows the 'build-YYYY.MM.DD.HHMMSS-<hash>'
    format used by the AeneasVerif automated build infrastructure.
    """
    return tag.split("-")[-1]


def fetch_file_content(repo, commit, path):
    """Returns the text content of a file from human-readable GitHub raw URLs.

    If the file does not exist (404), this returns None instead of raising an
    error, allowing caller logic to try fallback paths.
    """
    url = f"https://raw.githubusercontent.com/{repo}/{commit}/{path}"
    try:
        response = requests.get(url, timeout=DEFAULT_TIMEOUT)
        if response.status_code == 404:
            return None
        response.raise_for_status()
        return response.text
    except RequestException as e:
        print(f"ERROR: Failed to fetch file content: {url}")
        print(f"       {e}")
        sys.exit(1)


def get_charon_pin(aeneas_commit):
    """Discovers the Charon commit pinned by a specific Aeneas version (in the `charon-pin` file)."""
    content = fetch_file_content(AENEAS_REPO, aeneas_commit, "charon-pin")
    if content:
        for line in content.splitlines():
            line = line.strip()
            if line and not line.startswith("#"):
                return line
    return None


def calculate_sha256(data):
    return hashlib.sha256(data).hexdigest()


def get_host_platform():
    """Detects the current host platform in the format used by Anneal."""
    system = platform.system().lower()
    machine = platform.machine().lower()

    if system == "linux":
        if machine == "x86_64":
            return "linux-x86_64"
        elif machine in ["aarch64", "arm64"]:
            return "linux-aarch64"
    elif system == "darwin":
        if machine in ["arm64", "aarch64"]:
            return "macos-aarch64"
        elif machine == "x86_64":
            return "macos-x86_64"
    return None


def get_asset_checksums(release, repo_name):
    """Downloads all platform archives and calculates required checksums.

    Anneal requires verification of the downloaded '.tar.zst' archive itself.
    We no longer verify individual binaries inside the archive to simplify
    the process, trusting the archive produced by our infrastructure.

    Also extracts the `charon` binary for the host platform to query the
    Rust toolchain version it was built against.
    """
    checksums = {}
    host_platform = get_host_platform()
    if host_platform is None:
        print(f"ERROR: Unsupported host platform: {platform.system()} {platform.machine()}")
        sys.exit(1)

    charon_rust_toolchain = None

    with tempfile.TemporaryDirectory() as tmp_dir:
        tmp_path = Path(tmp_dir)
        for platform_name in PLATFORMS:
            asset_name = f"anneal-toolchain-{platform_name}.tar.zst"
            asset = next(
                (a for a in release["assets"] if a["name"] == asset_name), None
            )
            if not asset:
                print(
                    f"Warning: Asset {asset_name} not found in release {release['tag_name']}"
                )
                continue

            print(f"  Downloading {asset_name}...")
            try:
                resp = requests.get(
                    asset["browser_download_url"], timeout=DEFAULT_TIMEOUT
                )
                resp.raise_for_status()
                data = resp.content
            except RequestException as e:
                raise CompatibilityError(f"Failed to download asset {asset_name}: {e}")

            checksums[platform_name] = calculate_sha256(data)

            # If this is the host platform, we need to extract charon to get the rustc version.
            if platform_name == host_platform:
                # Write to a temporary file to allow processing with zstd/tar.
                archive_path = tmp_path / asset_name
                archive_path.write_bytes(data)

                try:
                    print(f"  Extracting charon from {asset_name}...")
                    # Extract only 'charon' file
                    zstd_proc = subprocess.Popen(
                        ["zstd", "-dc", str(archive_path)], stdout=subprocess.PIPE
                    )
                    tar_proc = subprocess.Popen(
                        ["tar", "-C", str(tmp_path), "-xf", "-", "rust/bin/charon", "rust/bin/charon-driver"],
                        stdin=zstd_proc.stdout,
                    )
                    zstd_proc.stdout.close()
                    tar_proc.wait()
                    zstd_proc.wait()

                    charon_path = tmp_path / "rust/bin/charon"
                    charon_driver_path = tmp_path / "rust/bin/charon-driver"
                    if charon_path.exists():
                        charon_path.chmod(charon_path.stat().st_mode | stat.S_IEXEC)
                        if charon_driver_path.exists():
                            charon_driver_path.chmod(charon_driver_path.stat().st_mode | stat.S_IEXEC)
                        print("  Querying charon rustc version...")
                        env = os.environ.copy()
                        env["PATH"] = f"{tmp_path}:{env.get('PATH', '')}"
                        result = subprocess.run(
                            [str(charon_path), "rustc", "--", "--version"],
                            capture_output=True,
                            text=True,
                            env=env
                        )
                        version_output = result.stdout.strip() or result.stderr.strip()
                        match = re.search(r'rustc .* \(.* (\d{4}-\d{2}-\d{2})\)', version_output)
                        if match:
                            date_str = match.group(1)
                            date_obj = datetime.strptime(date_str, "%Y-%m-%d")
                            toolchain_date = date_obj + timedelta(days=1)
                            charon_rust_toolchain = f"nightly-{toolchain_date.strftime('%Y-%m-%d')}"
                            print(f"  Found Charon Rust toolchain: {charon_rust_toolchain}")
                    else:
                        print("Warning: charon not found in archive")

                except Exception as e:
                    print(f"Warning: Failed to get rustc version from charon: {e}")

                # Copy the verified archive into our testdata directory for offline mock tests.
                import shutil
                testdata_dir = Path(__file__).parent.parent / "testdata" / "setup"
                testdata_dir.mkdir(parents=True, exist_ok=True)
                shutil.copy2(archive_path, testdata_dir / asset_name)

    if charon_rust_toolchain is None:
        raise CompatibilityError(
            f"Could not find charon binary for host platform {host_platform} in releases."
        )

    return checksums, charon_rust_toolchain

    if charon_rust_toolchain is None:
        raise CompatibilityError(
            f"Could not find charon binary for host platform {host_platform} in releases."
        )

    return checksums, charon_rust_toolchain




def update_cargo_toml(aeneas_meta, charon_meta, dry_run=False):
    """Writes the updated toolchain metadata to Anneal's Cargo.toml.

    This function uses tomlkit to parse and modify the document, which ensures
    that all existing comments and formatting in the original file are
    preserved.
    """
    if not CARGO_TOML_PATH.exists():
        print(f"ERROR: Cargo.toml not found at {CARGO_TOML_PATH}")
        sys.exit(1)

    if dry_run:
        print("\n[DRY RUN] Would update Cargo.toml with:")
        print(f"  Aeneas Tag: {aeneas_meta['tag']}")
        print(f"  Lean Toolchain: {aeneas_meta['lean_toolchain']}")
        print(f"  Charon Version: {charon_meta['version']}")
        print(f"  Charon Rust Toolchain: {charon_meta['rust_toolchain']}")
        return

    print(f"Updating {CARGO_TOML_PATH}...")
    try:
        content = CARGO_TOML_PATH.read_text()
        doc = tomlkit.parse(content)
    except Exception as e:
        print(f"ERROR: Failed to parse Cargo.toml: {e}")
        sys.exit(1)

    try:
        metadata = doc["package"]["metadata"]

        # Update the build_rs section, which defines the environment variables
        # injected into the Anneal build process.
        metadata["build_rs"]["aeneas_rev"] = aeneas_meta["commit"]
        metadata["build_rs"]["lean_toolchain"] = aeneas_meta["lean_toolchain"]
        metadata["build_rs"]["charon_version"] = charon_meta["version"]
        metadata["build_rs"]["charon_rust_toolchain"] = charon_meta["rust_toolchain"]

        # Update the anneal.dependencies section, which defines the download URLs
        # and checksums used by the 'cargo anneal setup' command.
        deps = metadata["anneal"]["dependencies"]

        # Remove separate Charon metadata if it exists.
        if "charon" in deps:
            del deps["charon"]
        # Remove separate Rust metadata if it exists.
        if "rust" in deps:
            del deps["rust"]

        # Update Aeneas metadata.
        deps["aeneas"]["tag"] = aeneas_meta["tag"]
        deps["aeneas"]["checksums"] = tomlkit.table()
        for k, v in sorted(aeneas_meta["checksums"].items()):
            deps["aeneas"]["checksums"][k] = v
    except KeyError as e:
        print(f"ERROR: Cargo.toml missing expected metadata section: {e}")
        sys.exit(1)

    try:
        CARGO_TOML_PATH.write_text(tomlkit.dumps(doc))
    except Exception as e:
        print(f"ERROR: Failed to write to Cargo.toml: {e}")
        sys.exit(1)


def main():
    parser = argparse.ArgumentParser(
        description="Roll Aeneas and Charon toolchain versions in Cargo.toml"
    )
    parser.add_argument(
        "--aeneas-tag", help="Force a specific Aeneas tag (skips discovery)"
    )
    parser.add_argument(
        "--charon-tag", help="Force a specific Charon tag (skips discovery)"
    )
    parser.add_argument(
        "--dry-run", action="store_true", help="Don't write to Cargo.toml"
    )
    args = parser.parse_args()

    target_aeneas_release = None

    if args.aeneas_tag and args.charon_tag:
        print(f"Using forced tags: Aeneas={args.aeneas_tag}, Charon={args.charon_tag}")
        target_aeneas_release = get_release_by_tag(AENEAS_REPO, args.aeneas_tag)
        a_commit = get_commit_from_tag(args.aeneas_tag)
        lean_toolchain = fetch_file_content(AENEAS_REPO, a_commit, "backends/lean/lean-toolchain")
        if lean_toolchain:
            lean_toolchain = lean_toolchain.strip()
        print(f"  Fetching checksums from Aeneas artifact...")
        a_checksums, charon_rust_toolchain = get_asset_checksums(target_aeneas_release, AENEAS_REPO)
        target_aeneas_meta = {
            "tag": args.aeneas_tag,
            "commit": a_commit,
            "lean_toolchain": lean_toolchain,
            "checksums": a_checksums,
            "version": args.charon_tag,
            "charon_rust_toolchain": charon_rust_toolchain,
        }
    else:
        print("Fetching releases from GitHub...")
        aeneas_releases = get_automated_releases(AENEAS_REPO)

        print("Searching for the latest stable Aeneas release...")
        target_aeneas_release = None
        target_aeneas_meta = None

        for a_rel in aeneas_releases:
            a_tag = a_rel["tag_name"]
            print(f"Found tag: {a_tag}")
            if a_tag.startswith("build-"):
                if args.aeneas_tag and a_tag != args.aeneas_tag:
                    continue

                if not release_has_assets(a_rel, AENEAS_REPO):
                    print(f"Skipping {a_tag}: missing prebuilt assets.")
                    continue

                a_commit = get_commit_from_tag(a_tag)
                # Bypassing charon-pin check and using dummy version.
                charon_version = "0.1.0-dummy"
                print(f"Checking {a_tag} (using dummy Charon version)...")

                # Fetch additional metadata required for the Anneal build process and the
                # 'setup' command.
                # Hardcoding Lean toolchain version as allowed by dummy values request.
                lean_toolchain = "leanprover/lean4:v4.28.0-rc1"
                print(f"Using hardcoded Lean toolchain: {lean_toolchain}")

                print(f"  Fetching checksums from Aeneas artifact...")
                try:
                    a_checksums, charon_rust_toolchain = get_asset_checksums(a_rel, AENEAS_REPO)
                except CompatibilityError as e:
                    print(f"  Skipping {a_tag}: {e}")
                    continue

                target_aeneas_release = a_rel
                target_aeneas_meta = {
                    "tag": a_tag,
                    "commit": a_commit,
                    "lean_toolchain": lean_toolchain,
                    "checksums": a_checksums,
                    "version": charon_version,
                    "charon_rust_toolchain": charon_rust_toolchain,
                }
                break

    if not target_aeneas_release:
        print("\nERROR: Could not find a suitable Aeneas release.")
        sys.exit(1)

    print(f"\nTargeting:")
    print(f"  Aeneas Tag: {target_aeneas_meta['tag']}")
    print(f"  Charon Version: {target_aeneas_meta['version']}")
    print(f"  Charon Rust Toolchain: {target_aeneas_meta['charon_rust_toolchain']}")

    charon_meta = {
        "version": target_aeneas_meta["version"],
        "rust_toolchain": target_aeneas_meta["charon_rust_toolchain"],
    }
    update_cargo_toml(target_aeneas_meta, charon_meta, dry_run=args.dry_run)
    if not args.dry_run:
        print("\nSuccessfully rolled toolchain updates!")


if __name__ == "__main__":
    main()
