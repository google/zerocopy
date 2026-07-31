#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# You may not use this file except in compliance with those licenses.

"""Regression tests for Cargo invocations outside cargo-zerocopy's grammar."""

import json
import os
from pathlib import Path
import re
import subprocess
import unittest
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
YQ = os.environ.get("YQ", "yq")


def workflow_object(name: str) -> dict[str, Any]:
    """Decodes a workflow with the parser pinned by check_actions.sh."""

    path = ROOT / ".github" / "workflows" / name
    result = subprocess.run(
        [
            YQ,
            "eval",
            "--output-format=json",
            "--no-colors",
            ".",
            "--",
            str(path),
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    parsed = json.loads(result.stdout)
    if not isinstance(parsed, dict):
        raise ValueError(f"{path} did not decode to a mapping")
    return parsed


class LockedCargoInvocationTests(unittest.TestCase):
    def test_toolchain_metadata_is_locked_and_offline(self):
        source = (
            ROOT / "zerocopy" / "ci" / "check_all_toolchains_tested.sh"
        ).read_text(encoding="utf-8")
        # Ignore prose and join shell continuation lines before looking for
        # commands. This covers both the original diff-based checker and its
        # later assignment-based implementation without coupling to either.
        source = "\n".join(
            line
            for line in source.splitlines()
            if not line.lstrip().startswith("#")
        )
        source = re.sub(r"\\\n\s*", " ", source)
        invocations = list(
            re.finditer(
                r"(?:^[ \t]*|[<(])"
                r"(?P<prefix>\./cargo\.sh\s+\+stable|cargo)\s+metadata\b"
                r"(?P<arguments>[^\n]*)",
                source,
                re.MULTILINE,
            )
        )
        self.assertEqual(len(invocations), 1)
        invocation = invocations[0]
        self.assertEqual(
            re.sub(r"\s+", " ", invocation.group("prefix")),
            "./cargo.sh +stable",
        )
        arguments = invocation.group("arguments")
        for flag in ("--locked", "--offline", "--no-deps"):
            with self.subTest(flag=flag):
                self.assertRegex(
                    arguments,
                    rf"(?:^|\s){re.escape(flag)}(?=\s|[|;)])",
                )

    def test_every_miri_nextest_run_has_an_inner_lock(self):
        workflow = workflow_object("ci.yml")
        runs = [
            step["run"]
            for job in workflow.get("jobs", {}).values()
            for step in job.get("steps", [])
            if isinstance(step, dict) and isinstance(step.get("run"), str)
        ]
        occurrences = []
        for run in runs:
            normalized = re.sub(r"\\\n\s*", " ", run)
            occurrences.extend(
                re.findall(r"\bmiri\s+nextest\s+run\b[^\n]*", normalized)
            )
        self.assertGreater(len(occurrences), 0)
        for invocation in occurrences:
            with self.subTest(invocation=invocation):
                self.assertRegex(
                    invocation,
                    r"^miri\s+nextest\s+run\s+--locked(?:\s|$)",
                )


if __name__ == "__main__":
    unittest.main()
