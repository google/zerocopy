#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# You may not use this file except in compliance with those licenses.

"""Mutation tests for Cargo-derived UI feature-profile eligibility."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = ROOT / ".github" / "workflows" / "ci.yml"
CHECKER = ROOT / "zerocopy" / "ci" / "check_all_toolchains_tested.sh"
YQ = os.environ.get("YQ", "yq")


def workflow_object() -> dict[str, Any]:
    result = subprocess.run(
        [
            YQ,
            "eval",
            "--output-format=json",
            "--no-colors",
            ".",
            "--",
            str(WORKFLOW),
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    parsed = json.loads(result.stdout)
    if not isinstance(parsed, dict):
        raise ValueError(f"{WORKFLOW} did not decode to a mapping")
    return parsed


class UiFeatureCoverageTests(unittest.TestCase):
    def run_checker(self, cells: list[str]) -> subprocess.CompletedProcess[str]:
        workflow = workflow_object()
        workflow["env"]["ZC_UI_TEST_CELLS"] = json.dumps(
            cells, separators=(",", ":")
        )

        with tempfile.TemporaryDirectory() as temporary_directory:
            temporary = Path(temporary_directory)
            workflow_path = temporary / "ci.yml"
            # JSON is a YAML subset. Serializing the decoded workflow avoids
            # coupling this mutation to one YAML spelling or parser library.
            workflow_path.write_text(json.dumps(workflow), encoding="utf-8")

            yq_path = shutil.which(YQ)
            if yq_path is None:
                self.fail(f"could not resolve yq executable {YQ!r}")
            (temporary / "yq").symlink_to(yq_path)

            environment = os.environ.copy()
            environment["PATH"] = (
                f"{temporary}{os.pathsep}{environment.get('PATH', '')}"
            )
            environment["ZEROCOPY_CI_WORKFLOW"] = str(workflow_path)
            return subprocess.run(
                [str(CHECKER)],
                cwd=ROOT / "zerocopy",
                env=environment,
                capture_output=True,
                text=True,
                check=False,
            )

    def test_rejects_newly_claimed_ineligible_default_profile(self):
        result = self.run_checker(
            [
                "zerocopy/default",
                "zerocopy/stable",
                "zerocopy/all",
                "zerocopy-derive/default",
            ]
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(
            "UI-test eligible cells contains unexpected entries:",
            result.stderr,
        )
        self.assertIn("zerocopy/default", result.stderr)

    def test_rejects_missing_eligible_stable_profile(self):
        result = self.run_checker(
            ["zerocopy/all", "zerocopy-derive/default"]
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(
            "UI-test eligible cells is missing required entries:",
            result.stderr,
        )
        self.assertIn("zerocopy/stable", result.stderr)


if __name__ == "__main__":
    unittest.main()
