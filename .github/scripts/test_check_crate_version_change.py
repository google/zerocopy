#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import importlib.util
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("check-crate-version-change.py")
SPEC = importlib.util.spec_from_file_location("version_change", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
version_change = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(version_change)


def manifest(name: str, version: str) -> bytes:
    return f'[package]\nname = "{name}"\nversion = "{version}"\n'.encode()


class InspectVersionsTests(unittest.TestCase):
    def inspect(self, current, previous, *, same=False, before="old"):
        return version_change.inspect_versions(
            current,
            before,
            lambda _before, path: previous.get(path),
            same,
        )

    def test_unchanged(self):
        current = [("a/Cargo.toml", manifest("a", "1.2.3"))]
        result = self.inspect(current, {current[0][0]: current[0][1]})
        self.assertFalse(result["changed"])
        self.assertEqual(result["version"], "1.2.3")
        self.assertFalse(result["prerelease"])

    def test_any_manifest_change_is_detected(self):
        current = [
            ("a/Cargo.toml", manifest("a", "2.0.0")),
            ("b/Cargo.toml", manifest("b", "2.0.0")),
        ]
        previous = {
            "a/Cargo.toml": manifest("a", "1.0.0"),
            "b/Cargo.toml": manifest("b", "2.0.0"),
        }
        self.assertTrue(self.inspect(current, previous, same=True)["changed"])

    def test_missing_previous_manifest_is_a_change(self):
        current = [("a/Cargo.toml", manifest("a", "1.0.0"))]
        self.assertTrue(self.inspect(current, {})["changed"])

    def test_package_rename_is_a_change(self):
        current = [("a/Cargo.toml", manifest("new-name", "1.0.0"))]
        previous = {"a/Cargo.toml": manifest("old-name", "1.0.0")}
        self.assertTrue(self.inspect(current, previous)["changed"])

    def test_prerelease_ignores_build_metadata(self):
        current = [("a/Cargo.toml", manifest("a", "1.0.0-rc.1+ci"))]
        result = self.inspect(current, {})
        self.assertTrue(result["prerelease"])

    def test_build_metadata_is_not_prerelease(self):
        current = [("a/Cargo.toml", manifest("a", "1.0.0+ci"))]
        result = self.inspect(current, {})
        self.assertFalse(result["prerelease"])

    def test_mismatched_release_versions_fail(self):
        current = [
            ("a/Cargo.toml", manifest("a", "1.0.0")),
            ("b/Cargo.toml", manifest("b", "2.0.0")),
        ]
        with self.assertRaisesRegex(ValueError, "versions disagree"):
            self.inspect(current, {}, same=True)

    def test_invalid_manifest_fails(self):
        with self.assertRaisesRegex(ValueError, "cannot read"):
            self.inspect([("bad", b"not toml")], {})


if __name__ == "__main__":
    unittest.main()
