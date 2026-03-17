#!/usr/bin/env python3

import requests
import json
import os
import hashlib
import tarfile
import tempfile
import sys
import argparse
from pathlib import Path
import tomlkit
from requests.exceptions import RequestException

# Default timeout for all network requests in seconds.
DEFAULT_TIMEOUT = 30

# Configuration for the Aeneas and Charon repositories. These are used to discover
# releases and fetch metadata from the AeneasVerif organization on GitHub.
AENEAS_REPO = "AeneasVerif/aeneas"
CHARON_REPO = "AeneasVerif/charon"

# The set of platforms that Hermes supports for pre-built binaries. The script
# will download and checksum artifacts for each of these triples.
PLATFORMS = ["linux-x86_64", "macos-aarch64", "macos-x86_64"]

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


def get_asset_checksums(release, repo_name):
    """Downloads all platform archives and calculates required checksums.

    Hermes requires two levels of verification:
    1. The checksum of the downloaded '.tar.gz' archive itself.
    2. The checksum of the primary binaries contained within the archive (e.g.,
       'aeneas', 'charon').

    The latter allows Hermes to detect and repair corruption of individual
    binaries in a local toolchain installation.
    """
    checksums = {}

    with tempfile.TemporaryDirectory() as tmp_dir:
        tmp_path = Path(tmp_dir)
        for platform in PLATFORMS:
            asset_name = f"{repo_name.split('/')[-1]}-{platform}.tar.gz"
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
                print(f"ERROR: Failed to download asset {asset_name}")
                print(f"       {e}")
                sys.exit(1)

            checksums[platform] = calculate_sha256(data)

            # Write to a temporary file to allow processing with tarfile.
            archive_path = tmp_path / asset_name
            archive_path.write_bytes(data)

            try:
                with tarfile.open(archive_path, "r:gz") as tar:
                    found_binaries = set()
                    for member in tar.getmembers():
                        # We extract and checksum only the primary binaries that
                        # Hermes needs to verify individually.
                        name = Path(member.name).name
                        if name in ["charon", "charon-driver", "aeneas"]:
                            f = tar.extractfile(member)
                            if f is None:
                                print(
                                    f"Warning: Could not extract {name} from {asset_name} (likely not a regular file)"
                                )
                                continue
                            binary_data = f.read()
                            checksums[f"{platform}-{name}"] = calculate_sha256(
                                binary_data
                            )
                            found_binaries.add(name)

                    # Verify that we found the expected binaries for this repo.
                    expected = (
                        ["aeneas"]
                        if repo_name.lower().endswith("/aeneas")
                        else ["charon", "charon-driver"]
                    )
                    missing = [b for b in expected if b not in found_binaries]
                    if missing:
                        print(
                            f"ERROR: Release {release['tag_name']} for {platform} is missing expected binaries: {', '.join(missing)}"
                        )
                        sys.exit(1)
            except tarfile.TarError as e:
                print(f"ERROR: Failed to extract archive {asset_name}: {e}")
                sys.exit(1)

    return checksums


def update_cargo_toml(aeneas_meta, charon_meta, dry_run=False):
    """Writes the updated toolchain metadata to Hermes's Cargo.toml.

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
        print(f"  Charon Tag: {charon_meta['tag']}")
        print(f"  Lean Toolchain: {aeneas_meta['lean_toolchain']}")
        print(f"  Charon Version: {charon_meta['version']}")
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

        # Update the build-rs section, which defines the environment variables
        # injected into the Hermes build process.
        build_rs = metadata["build-rs"]
        build_rs["aeneas_rev"] = aeneas_meta["commit"]
        build_rs["lean_toolchain"] = aeneas_meta["lean_toolchain"]
        build_rs["charon_version"] = charon_meta["version"]

        # Update the hermes.dependencies section, which defines the download URLs
        # and checksums used by the 'cargo hermes setup' command.
        deps = metadata["hermes"]["dependencies"]

        # Update Charon metadata.
        deps["charon"]["tag"] = charon_meta["tag"]
        for k, v in charon_meta["checksums"].items():
            deps["charon"]["checksums"][k] = v

        # Update Aeneas metadata.
        deps["aeneas"]["tag"] = aeneas_meta["tag"]
        for k, v in aeneas_meta["checksums"].items():
            deps["aeneas"]["checksums"][k] = v
    except KeyError as e:
        print(f"ERROR: Cargo.toml missing expected metadata section: {e}")
        print(
            "Expected structure: [package.metadata.build-rs] and [package.metadata.hermes.dependencies]"
        )
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
    target_charon_release = None

    if args.aeneas_tag and args.charon_tag:
        print(f"Using forced tags: Aeneas={args.aeneas_tag}, Charon={args.charon_tag}")
        target_aeneas_release = get_release_by_tag(AENEAS_REPO, args.aeneas_tag)
        target_charon_release = get_release_by_tag(CHARON_REPO, args.charon_tag)
    else:
        print("Fetching releases from GitHub...")
        aeneas_releases = get_automated_releases(AENEAS_REPO)
        charon_releases = get_automated_releases(CHARON_REPO)

        print("Searching for a compatible pair of Aeneas and Charon releases...")
        for a_rel in aeneas_releases:
            a_tag = a_rel["tag_name"]

            # If the user specified an Aeneas tag, skip all others until we find
            # the exact match.
            if args.aeneas_tag and a_tag != args.aeneas_tag:
                continue

            a_commit = get_commit_from_tag(a_tag)
            c_commit = get_charon_pin(a_commit)

            if not c_commit:
                print(f"Skipping {a_tag}: could not find charon-pin file.")
                continue

            # Find a Charon release that matches the pin in Aeneas. Sometimes
            # Aeneas pins a Charon commit that hasn't finished its automated
            # build yet; in this case, we search back through history for the
            # last stable pair.
            c_rel = next(
                (r for r in charon_releases if r["tag_name"].endswith(f"-{c_commit}")),
                None,
            )
            if c_rel:
                # If the user specified a Charon tag override, verify that it
                # actually matches the pin in the Aeneas version we found.
                if args.charon_tag and c_rel["tag_name"] != args.charon_tag:
                    print(
                        f"Skipping {a_tag}: pins Charon {c_commit[:8]} but user requested {args.charon_tag}"
                    )
                    continue

                target_aeneas_release = a_rel
                target_charon_release = c_rel
                print(f"Found compatible pair!")
                break
            else:
                print(
                    f"Skipping {a_tag}: pins Charon {c_commit[:8]} which has no release."
                )

    if not target_aeneas_release or not target_charon_release:
        print(
            "\nERROR: Could not find a compatible pair of Aeneas and Charon releases."
        )
        sys.exit(1)

    a_tag = target_aeneas_release["tag_name"]
    a_commit = get_commit_from_tag(a_tag)
    c_tag = target_charon_release["tag_name"]
    c_commit = get_commit_from_tag(c_tag)

    print(f"\nTargeting:")
    print(f"  Aeneas: {a_tag}")
    print(f"  Charon: {c_tag}")

    # Fetch additional metadata required for the Hermes build process and the
    # 'setup' command.
    print("Fetching toolchain versions...")
    lean_toolchain = fetch_file_content(
        AENEAS_REPO, a_commit, "backends/lean/lean-toolchain"
    )
    if not lean_toolchain:
        print(
            f"ERROR: Could not find backends/lean/lean-toolchain in Aeneas at {a_commit}"
        )
        sys.exit(1)
    lean_toolchain = lean_toolchain.strip()

    charon_cargo = fetch_file_content(CHARON_REPO, c_commit, "charon/Cargo.toml")
    charon_version = tomlkit.parse(charon_cargo)["package"]["version"]

    print(f"Fetching checksums for Aeneas...")
    a_checksums = get_asset_checksums(target_aeneas_release, AENEAS_REPO)

    print(f"Fetching checksums for Charon...")
    c_checksums = get_asset_checksums(target_charon_release, CHARON_REPO)

    # Bundle all discovered metadata into structured objects for the update logic.
    aeneas_meta = {
        "tag": a_tag,
        "commit": a_commit,
        "lean_toolchain": lean_toolchain,
        "checksums": a_checksums,
    }

    charon_meta = {
        "tag": c_tag,
        "commit": c_commit,
        "version": charon_version,
        "checksums": c_checksums,
    }

    update_cargo_toml(aeneas_meta, charon_meta, dry_run=args.dry_run)
    if not args.dry_run:
        print("\nSuccessfully rolled toolchain updates!")


if __name__ == "__main__":
    main()
