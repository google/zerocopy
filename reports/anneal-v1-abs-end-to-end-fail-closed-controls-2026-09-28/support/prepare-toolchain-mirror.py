#!/usr/bin/env python3
"""Make a disposable V1-compatible view of an already installed toolchain."""

import argparse
import hashlib
import json
from pathlib import Path


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


parser = argparse.ArgumentParser()
parser.add_argument("--source-base", required=True, type=Path,
                    help="base containing anneal/toolchain/<slug>")
parser.add_argument("--destination-base", required=True, type=Path,
                    help="new base directory for the disposable mirror")
parser.add_argument("--slug", required=True,
                    help="toolchain directory name below anneal/toolchain")
args = parser.parse_args()

source_root = args.source_base / "anneal" / "toolchain" / args.slug
dest_root = args.destination_base / "anneal" / "toolchain" / args.slug
if not source_root.is_dir():
    parser.error(f"toolchain root does not exist: {source_root}")
if dest_root.exists():
    parser.error(f"destination already exists: {dest_root}")

(dest_root / "aeneas" / "backends").mkdir(parents=True)
(dest_root / "aeneas" / "bin").symlink_to(
    source_root / "aeneas" / "bin", target_is_directory=True
)
for name in ("lean", "rust"):
    (dest_root / name).symlink_to(source_root / name, target_is_directory=True)

source_lean = (source_root / "aeneas" / "backends" / "lean").resolve()
dest_lean = dest_root / "aeneas" / "backends" / "lean"
dest_lean.mkdir()
for item in source_lean.iterdir():
    if item.name == "lake-manifest.json":
        continue
    (dest_lean / item.name).symlink_to(item, target_is_directory=item.is_dir())

manifest_path = source_lean / "lake-manifest.json"
manifest = json.loads(manifest_path.read_text())
packages = []
for entry in manifest["packages"]:
    entry["type"] = "path"
    entry["dir"] = f".lake/packages/{entry['name']}"
    if not (source_lean / entry["dir"]).is_dir():
        parser.error(f"missing preinstalled package tree: {entry['dir']}")
    packages.append({
        "name": entry["name"],
        "dir": entry["dir"],
        "rev": entry.get("rev"),
    })
(dest_lean / "lake-manifest.json").write_text(
    json.dumps(manifest, indent=2) + "\n"
)

print(json.dumps({
    "destination_root": str(dest_root),
    "source_manifest_sha256": sha256(manifest_path),
    "mirror_manifest_sha256": sha256(dest_lean / "lake-manifest.json"),
    "packages": packages,
}, indent=2))
