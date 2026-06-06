#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for check-release-pr-files.py."""

from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path


SCRIPT = Path(__file__).resolve().parent / "check-release-pr-files.py"
SPEC = importlib.util.spec_from_file_location("check_release_pr_files", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
check_release_pr_files = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(check_release_pr_files)


class ReleasePrFileTests(unittest.TestCase):
    def test_porcelain_status_paths_include_untracked_and_renames(self) -> None:
        status = " M anneal/Cargo.toml\n?? anneal/release-metadata/linux.json\nR  old/path -> anneal/README.md\n"
        self.assertEqual(
            check_release_pr_files.parse_porcelain_status_paths(status),
            ["anneal/Cargo.toml", "anneal/release-metadata/linux.json", "old/path", "anneal/README.md"],
        )

    def test_validation_catches_unexpected_and_missing_files(self) -> None:
        errors = check_release_pr_files.validation_errors(
            ["anneal/Cargo.toml", "anneal/release-metadata/linux.json"],
            ["anneal/Cargo.toml", "anneal/Cargo.lock", "anneal/README.md"],
            ["anneal/Cargo.toml", "anneal/README.md"],
        )
        self.assertEqual(len(errors), 2)
        self.assertIn("anneal/release-metadata/linux.json", errors[0])
        self.assertIn("anneal/README.md", errors[1])


if __name__ == "__main__":
    unittest.main()
