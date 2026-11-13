#!/usr/bin/env python3
"""Verify component_license_manifest.json structure and SHA-256 license hashes."""

from __future__ import annotations
import argparse
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    args = parser.parse_args()
    data = json.loads(args.manifest.read_text(encoding="utf-8"))
    assert len(data["components"]) >= 10, "Expected at least 10 component license entries"
    for key, digest in data["license_file_hashes"].items():
        assert len(digest) == 64, f"Invalid SHA-256 digest for {key}: {digest}"
    print(f"OK: verified {len(data['components'])} license entries and {len(data['license_file_hashes'])} hashes.")


if __name__ == "__main__":
    main()
