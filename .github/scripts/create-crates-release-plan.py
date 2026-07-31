#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Create the immutable input consumed by reconcile-crates-release.py."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import tomllib
from pathlib import Path


SHA_RE = re.compile(r"[0-9a-f]{40}")


def package_entry(root: Path, spec: str) -> dict[str, str]:
    try:
        expected_name, manifest_arg, archive_arg = spec.split("=", 2)
    except ValueError as err:
        raise ValueError(
            "package must be NAME=MANIFEST_PATH=ARCHIVE_PATH"
        ) from err

    manifest_path = Path(manifest_arg)
    archive_path = Path(archive_arg)
    manifest = tomllib.loads((root / manifest_path).read_text(encoding="utf-8"))
    try:
        name = manifest["package"]["name"]
        version = manifest["package"]["version"]
    except (KeyError, TypeError) as err:
        raise ValueError(
            f"{manifest_path}: missing package name or version"
        ) from err
    if name != expected_name:
        raise ValueError(
            f"{manifest_path}: expected package {expected_name!r}, "
            f"found {name!r}"
        )
    expected_archive = f"{name}-{version}.crate"
    if archive_path.name != expected_archive:
        raise ValueError(
            f"{archive_path}: expected archive filename {expected_archive!r}"
        )
    contents = (root / archive_path).read_bytes()
    return {
        "name": name,
        "version": version,
        "manifest_path": manifest_path.as_posix(),
        "archive_path": archive_path.as_posix(),
        "sha256": hashlib.sha256(contents).hexdigest(),
    }


def create_plan(
    *,
    root: Path,
    repository: str,
    tag: str,
    sha: str,
    workflow: str,
    environment: str,
    prerelease: bool,
    cargo_command: list[str],
    package_specs: list[str],
) -> dict[str, object]:
    if not SHA_RE.fullmatch(sha):
        raise ValueError("sha must be a lowercase 40-character commit SHA")
    if not cargo_command:
        raise ValueError("cargo command cannot be empty")
    packages = [package_entry(root, spec) for spec in package_specs]
    if not packages:
        raise ValueError("at least one package is required")
    names = [package["name"] for package in packages]
    if len(names) != len(set(names)):
        raise ValueError("package names must be unique")
    return {
        "schema": 1,
        "repository": repository,
        "tag": tag,
        "sha": sha,
        "workflow": workflow,
        "environment": environment,
        "prerelease": prerelease,
        "cargo_command": cargo_command,
        "packages": packages,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument("--repository", required=True)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--sha", required=True)
    parser.add_argument("--workflow", required=True)
    parser.add_argument("--environment", required=True)
    parser.add_argument("--prerelease", action="store_true")
    parser.add_argument("--cargo-command", action="append", required=True)
    parser.add_argument("--package", action="append", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        plan = create_plan(
            root=args.root,
            repository=args.repository,
            tag=args.tag,
            sha=args.sha,
            workflow=args.workflow,
            environment=args.environment,
            prerelease=args.prerelease,
            cargo_command=args.cargo_command,
            package_specs=args.package,
        )
        args.output.write_text(
            json.dumps(plan, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    except (OSError, ValueError, tomllib.TOMLDecodeError) as err:
        print(f"error: {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
