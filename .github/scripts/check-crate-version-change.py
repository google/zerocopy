#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Compare crate versions with the complete pre-push repository state.

Release workflows must compare against `github.event.before`, not `HEAD^`.
A push can contain multiple commits, so `HEAD^` can miss a version bump earlier
in the push. This helper also treats a missing prior commit or manifest as a
change, which keeps first releases and unusual GitHub push events fail-safe.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tomllib
from pathlib import Path
from typing import Callable, Sequence


GitShow = Callable[[str, str], bytes | None]


def _manifest_version(contents: bytes, path: str) -> tuple[str, str]:
    try:
        package = tomllib.loads(contents.decode())["package"]
        name = package["name"]
        version = package["version"]
    except (
        KeyError,
        TypeError,
        UnicodeDecodeError,
        tomllib.TOMLDecodeError,
    ) as err:
        raise ValueError(f"{path}: cannot read package name and version: {err}")
    if not isinstance(name, str) or not isinstance(version, str):
        raise ValueError(f"{path}: package name and version must be strings")
    return name, version


def inspect_versions(
    manifests: Sequence[tuple[str, bytes]],
    before: str,
    git_show: GitShow,
    require_same_version: bool,
) -> dict[str, object]:
    current = {
        path: _manifest_version(contents, path)
        for path, contents in manifests
    }
    versions = {version for _, version in current.values()}
    if require_same_version and len(versions) != 1:
        rendered = ", ".join(
            f"{name}={version}" for name, version in current.values()
        )
        raise ValueError(f"release crate versions disagree: {rendered}")

    previous: dict[str, tuple[str, str] | None] = {}
    changed = False
    for path, _ in manifests:
        old_contents = git_show(before, path)
        if old_contents is None:
            previous[path] = None
            changed = True
            continue
        old = _manifest_version(old_contents, f"{before}:{path}")
        previous[path] = old
        # A rename is just as release-relevant as a version change. The
        # workflow's trusted package plan will then either be updated in the
        # same change or fail explicitly; never silently skip a renamed crate.
        if old != current[path]:
            changed = True

    version = next(iter(versions)) if len(versions) == 1 else None
    prerelease = version is not None and "-" in version.split("+", 1)[0]
    return {
        "changed": changed,
        "version": version,
        "prerelease": prerelease,
        "current": {
            path: {"name": name, "version": crate_version}
            for path, (name, crate_version) in current.items()
        },
        "previous": {
            path: (
                None
                if value is None
                else {"name": value[0], "version": value[1]}
            )
            for path, value in previous.items()
        },
    }


def _git_show(before: str, path: str) -> bytes | None:
    # The all-zero SHA marks a branch creation. Treat it exactly like a missing
    # commit rather than asking Git to resolve an invalid object name.
    if before and set(before) == {"0"}:
        return None
    result = subprocess.run(
        ["git", "show", f"{before}:{path}"],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )
    if result.returncode != 0:
        return None
    return result.stdout


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--before", required=True)
    parser.add_argument("--manifest", action="append", required=True)
    parser.add_argument("--require-same-version", action="store_true")
    args = parser.parse_args()

    try:
        manifests = [(path, Path(path).read_bytes()) for path in args.manifest]
        result = inspect_versions(
            manifests,
            args.before,
            _git_show,
            args.require_same_version,
        )
    except (OSError, ValueError) as err:
        print(f"error: {err}", file=sys.stderr)
        return 1
    json.dump(result, sys.stdout, indent=2, sort_keys=True)
    print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
