#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Check that release automation only changed expected files."""

from __future__ import annotations

import argparse
import subprocess
from collections.abc import Iterable


def parse_porcelain_status_paths(status: str) -> list[str]:
    paths = []
    for line in status.splitlines():
        if not line:
            continue
        path = line[3:]
        if " -> " in path:
            old, new = path.split(" -> ", 1)
            paths.extend([old, new])
        else:
            paths.append(path)
    return paths


def tracked_diff_paths() -> list[str]:
    output = subprocess.check_output(["git", "diff", "--name-only"], text=True)
    return [line for line in output.splitlines() if line]


def working_tree_status_paths() -> list[str]:
    output = subprocess.check_output(
        ["git", "status", "--porcelain=v1", "--untracked-files=all"], text=True
    )
    return parse_porcelain_status_paths(output)


def unexpected_paths(paths: Iterable[str], allowed: Iterable[str]) -> list[str]:
    return sorted(set(paths) - set(allowed))


def validation_errors(paths: Iterable[str], allowed: Iterable[str], required: Iterable[str]) -> list[str]:
    path_set = set(paths)
    errors = []
    unexpected = unexpected_paths(path_set, allowed)
    if unexpected:
        errors.append("Unexpected files changed:\n" + "\n".join(unexpected))
    missing_required = sorted(set(required) - path_set)
    if missing_required:
        errors.append("Required files were not changed:\n" + "\n".join(missing_required))
    return errors


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--allowed", action="append", default=[], required=True)
    parser.add_argument("--required", action="append", default=[])
    parser.add_argument("--include-untracked", action="store_true")
    parser.add_argument("--context", default="release workflow")
    args = parser.parse_args()

    paths = working_tree_status_paths() if args.include_untracked else tracked_diff_paths()
    errors = validation_errors(paths, args.allowed, args.required)
    if errors:
        print(f"::error::{args.context} changed unexpected files or missed required updates.")
        for error in errors:
            print(error)
        raise SystemExit(1)


if __name__ == "__main__":
    main()
