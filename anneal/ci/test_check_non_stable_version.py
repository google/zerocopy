# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `anneal/ci/check_non_stable_version.sh`."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parent / "check_non_stable_version.sh"


def run_check(*args, cwd=None, env=None):
    return subprocess.run(
        [str(SCRIPT), *args],
        cwd=cwd,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )


class CheckNonStableVersionTests(unittest.TestCase):
    def run_for_manifest(self, content, *, relative=False):
        with tempfile.TemporaryDirectory(prefix="anneal-semver-test-") as tmp:
            manifest = Path(tmp) / "Cargo.toml"
            manifest.write_text(content, encoding="utf-8")
            if relative:
                return run_check("Cargo.toml", cwd=tmp)
            return run_check(str(manifest))

    def run_for_version(self, version, *, relative=False):
        content = f'[package]\nname = "cargo-anneal"\nversion = {json.dumps(version)}\n'
        return self.run_for_manifest(content, relative=relative)

    def test_default_repo_manifest_passes(self):
        result = run_check()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("trusted/cargo-anneal/Cargo.toml", result.stdout)

    def test_accepts_valid_prerelease_versions_with_optional_build_metadata(self):
        valid_versions = (
            "0.2.0-alpha.4",
            "0.2.0-alpha.4+build.1",
            "0.2.0-rc.1+20261122.sha.5114f85",
            "1.0.0-0.3.7",
            "1.0.0-x-y-z.--",
            "0.1.0-0a+001",
        )
        for version in valid_versions:
            with self.subTest(version=version):
                result = self.run_for_version(version)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn(version, result.stdout)

        relative = self.run_for_version("0.2.0-alpha.4+build.1", relative=True)
        self.assertEqual(relative.returncode, 0, relative.stderr)

    def test_rejects_stable_versions(self):
        stable_versions = (
            "0.1.0",
            "0.2.0",
            "1.0.0",
            "0.2.0+build.1",
            "1.0.0+build-1",
            "1.0.0+20130313144700",
        )
        for version in stable_versions:
            with self.subTest(version=version):
                result = self.run_for_version(version)
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertNotIn("Traceback", result.stderr)
                self.assertIn("not a valid SemVer 2.0.0 pre-release", result.stderr)

    def test_rejects_invalid_semver_strings(self):
        invalid_versions = (
            "01.2.0-alpha.1",
            "0.02.0-alpha.1",
            "0.2.01-alpha.1",
            "0.2.0-alpha.01",
            "0.2.0-01",
            "0.2.0-",
            "0.2.0-.alpha",
            "0.2.0-alpha.",
            "0.2.0-alpha..1",
            "0.2.0-alpha.1+",
            "0.2.0-alpha.1+.1",
            "0.2.0-alpha.1+build..2",
            "0.2.0-alpha_1",
            "v0.2.0-alpha.1",
            "0.2.0-alpha.1\n",
        )
        for version in invalid_versions:
            with self.subTest(version=version):
                result = self.run_for_version(version)
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertNotIn("Traceback", result.stderr)
                self.assertIn("not a valid SemVer 2.0.0 pre-release", result.stderr)

    def test_rejects_malformed_manifests_and_invalid_cli_args(self):
        manifest_cases = (
            ("missing_package", '[workspace]\nmembers = []\n', "does not define a [package] table"),
            ("non_table_package", 'package = "cargo-anneal"\n', "does not define a [package] table"),
            ("missing_version", '[package]\nname = "cargo-anneal"\n', "does not specify package.version"),
            ("empty_version", '[package]\nname = "cargo-anneal"\nversion = ""\n', "does not specify package.version"),
            ("integer_version", '[package]\nname = "cargo-anneal"\nversion = 123\n', "does not specify package.version"),
            ("boolean_version", '[package]\nname = "cargo-anneal"\nversion = true\n', "does not specify package.version"),
            ("malformed_toml", '[package\nversion = "0.2.0-alpha.1"\n', "Error reading "),
        )
        for label, content, expected_err in manifest_cases:
            with self.subTest(case=label):
                result = self.run_for_manifest(content)
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertNotIn("Traceback", result.stderr)
                self.assertIn(expected_err, result.stderr)

        with tempfile.TemporaryDirectory(prefix="anneal-semver-missing-") as tmp:
            missing_file = Path(tmp) / "does-not-exist.toml"
            missing = run_check(str(missing_file))
            self.assertEqual(missing.returncode, 1, missing.stdout)
            self.assertNotIn("Traceback", missing.stderr)
            self.assertIn("Error reading ", missing.stderr)

        empty_arg = run_check("")
        self.assertEqual(empty_arg.returncode, 1, empty_arg.stdout)
        self.assertIn("manifest path must not be empty", empty_arg.stderr)

        extra_args = run_check("a", "b")
        self.assertEqual(extra_args.returncode, 1, extra_args.stdout)
        self.assertIn("Usage:", extra_args.stderr)

    def test_isolated_python_blocks_pythonpath_shadowing_and_pycache(self):
        with tempfile.TemporaryDirectory(prefix="anneal-semver-iso-") as tmp:
            tmp_path = Path(tmp)
            manifest = tmp_path / "Cargo.toml"
            manifest.write_text(
                '[package]\nname = "cargo-anneal"\nversion = "0.2.0-alpha.8"\n',
                encoding="utf-8",
            )
            poison = tmp_path / "poison"
            poison.mkdir()
            (poison / "tomllib.py").write_text(
                'raise RuntimeError("shadowed tomllib")\n', encoding="utf-8"
            )
            (poison / "re.py").write_text(
                'raise RuntimeError("shadowed re")\n', encoding="utf-8"
            )
            env = os.environ.copy()
            env["PYTHONPATH"] = str(poison)
            result = run_check(str(manifest), cwd=poison, env=env)
            if sys.version_info >= (3, 11):
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertFalse((poison / "__pycache__").exists())
            else:
                self.assertFalse((poison / "__pycache__").exists())
