#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import hashlib
import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("create-crates-release-plan.py")
SPEC = importlib.util.spec_from_file_location("create_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
create_plan = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(create_plan)


class CreatePlanTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        (self.root / "crate").mkdir()
        (self.root / "artifacts").mkdir()
        (self.root / "crate/Cargo.toml").write_text(
            '[package]\nname = "demo"\nversion = "1.2.3"\n',
            encoding="utf-8",
        )
        self.archive = self.root / "artifacts/demo-1.2.3.crate"
        self.archive.write_bytes(b"crate contents")

    def tearDown(self):
        self.temporary.cleanup()

    def make_plan(
        self,
        package="demo=crate/Cargo.toml=artifacts/demo-1.2.3.crate",
    ):
        return create_plan.create_plan(
            root=self.root,
            repository="google/zerocopy",
            tag="v1.2.3",
            sha="a" * 40,
            workflow="release.yml",
            environment="release",
            prerelease=False,
            cargo_command=["cargo"],
            package_specs=[package],
        )

    def test_complete_plan(self):
        plan = self.make_plan()
        self.assertEqual(plan["schema"], 1)
        self.assertEqual(plan["packages"][0]["version"], "1.2.3")
        self.assertEqual(
            plan["packages"][0]["sha256"],
            hashlib.sha256(b"crate contents").hexdigest(),
        )

    def test_package_name_must_match(self):
        with self.assertRaisesRegex(ValueError, "expected package"):
            self.make_plan("wrong=crate/Cargo.toml=artifacts/demo-1.2.3.crate")

    def test_archive_name_must_match(self):
        wrong = self.root / "artifacts/wrong.crate"
        wrong.write_bytes(b"crate contents")
        with self.assertRaisesRegex(ValueError, "expected archive filename"):
            self.make_plan("demo=crate/Cargo.toml=artifacts/wrong.crate")

    def test_commit_must_be_full_sha(self):
        with self.assertRaisesRegex(ValueError, "40-character"):
            create_plan.create_plan(
                root=self.root,
                repository="google/zerocopy",
                tag="v1.2.3",
                sha="HEAD",
                workflow="release.yml",
                environment="release",
                prerelease=False,
                cargo_command=["cargo"],
                package_specs=[
                    "demo=crate/Cargo.toml=artifacts/demo-1.2.3.crate"
                ],
            )

    def test_cli_accepts_option_like_cargo_command_arguments(self):
        output = self.root / "plan.json"
        subprocess.run(
            [
                sys.executable,
                SCRIPT,
                "--root",
                self.root,
                "--repository",
                "google/zerocopy",
                "--tag",
                "v1.2.3",
                "--sha",
                "a" * 40,
                "--workflow",
                "release.yml",
                "--environment",
                "release",
                "--cargo-command",
                "ci/run_cargo_for_release.sh",
                "--cargo-command=--prebuilt",
                "--cargo-command=--source-root",
                "--cargo-command",
                "release-source/zerocopy",
                "--cargo-command",
                "+stable",
                "--package",
                "demo=crate/Cargo.toml=artifacts/demo-1.2.3.crate",
                "--output",
                output,
            ],
            check=True,
        )
        plan = json.loads(output.read_text(encoding="utf-8"))
        self.assertEqual(
            plan["cargo_command"],
            [
                "ci/run_cargo_for_release.sh",
                "--prebuilt",
                "--source-root",
                "release-source/zerocopy",
                "+stable",
            ],
        )


if __name__ == "__main__":
    unittest.main()
