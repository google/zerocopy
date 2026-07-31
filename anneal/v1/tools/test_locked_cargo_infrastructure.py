#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Regression tests for Anneal's locked Docker dependency build."""

import json
from pathlib import Path
import subprocess
import unittest


_ROOT = Path(__file__).resolve().parents[3]
_DOCKERFILE = _ROOT / "anneal" / "v1" / "Dockerfile"
_MANIFEST = _ROOT / "anneal" / "v1" / "Cargo.toml"


class LockedCargoInfrastructureTest(unittest.TestCase):
    def test_docker_cache_build_uses_the_real_locked_workspace(self):
        dockerfile = _DOCKERFILE.read_text(encoding="utf-8")
        for required in (
            "COPY --chown=anneal:anneal anneal/v1/Cargo.toml ./Cargo.toml",
            "COPY --chown=anneal:anneal anneal/v1/Cargo.lock ./",
            "anneal/v1/tools/doc_gen/Cargo.toml ./tools/doc_gen/Cargo.toml",
            "cargo build --locked --workspace",
            "cargo build --locked --workspace --tests",
        ):
            with self.subTest(required=required):
                self.assertIn(required, dockerfile)

        self.assertNotIn("Cargo.toml.no_workspace", dockerfile)
        self.assertNotIn("sed '1,2d' Cargo.toml", dockerfile)

    def test_repository_lock_resolves_both_workspace_members_offline(self):
        result = subprocess.run(
            [
                "cargo",
                "metadata",
                "--locked",
                "--offline",
                "--no-deps",
                "--format-version",
                "1",
                "--manifest-path",
                str(_MANIFEST),
            ],
            cwd=_ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        package_names = {
            package["name"] for package in json.loads(result.stdout)["packages"]
        }
        self.assertEqual(package_names, {"cargo-anneal", "doc_gen"})


if __name__ == "__main__":
    unittest.main()
