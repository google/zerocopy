#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

from __future__ import annotations

import importlib.util
import pathlib
import sys
import unittest


_SCRIPT = pathlib.Path(__file__).with_name("check.py")
_SPEC = importlib.util.spec_from_file_location("require_successful_jobs", _SCRIPT)
assert _SPEC is not None and _SPEC.loader is not None
checker = importlib.util.module_from_spec(_SPEC)
sys.modules[_SPEC.name] = checker
_SPEC.loader.exec_module(checker)


class RequireSuccessfulJobsTests(unittest.TestCase):
    def evaluate(
        self,
        results: dict[str, str],
        *,
        cancelled: bool = False,
        allowed: list[str] | None = None,
    ) -> list[str]:
        return checker.evaluate(
            results,
            workflow_cancelled=cancelled,
            allowed_skipped_jobs=[] if allowed is None else allowed,
        )

    def test_all_jobs_must_succeed(self) -> None:
        self.assertEqual(self.evaluate({"build": "success", "test": "success"}), [])
        for result in ("failure", "cancelled"):
            with self.subTest(result=result):
                self.assertEqual(
                    self.evaluate({"build": result}),
                    [f"build concluded {result}"],
                )

    def test_only_explicit_skips_are_allowed(self) -> None:
        self.assertEqual(
            self.evaluate({"build": "success", "miri": "skipped"}, allowed=["miri"]),
            [],
        )
        self.assertEqual(
            self.evaluate({"miri": "skipped"}),
            ["miri was unexpectedly skipped"],
        )
        self.assertEqual(
            self.evaluate({"miri": "failure"}, allowed=["miri"]),
            ["miri concluded failure"],
        )

    def test_skip_policy_must_name_a_dependency(self) -> None:
        self.assertEqual(
            self.evaluate({"build": "success"}, allowed=["miri"]),
            ["skip policy names jobs absent from needs: miri"],
        )

    def test_workflow_cancellation_fails_the_gate(self) -> None:
        self.assertEqual(
            self.evaluate({"build": "success"}, cancelled=True),
            ["the workflow is cancelled"],
        )

    def test_inputs_fail_closed(self) -> None:
        with self.assertRaises(checker.InputError):
            checker.job_results({})
        with self.assertRaises(checker.InputError):
            checker.job_results({"build": {"result": "neutral"}})
        with self.assertRaises(checker.InputError):
            checker.job_results({"build": {}})
        with self.assertRaises(checker.InputError):
            checker.parse_allowed_skips('["miri", "miri"]')
        with self.assertRaises(checker.InputError):
            checker.parse_cancelled("False")

    def test_summary_exposes_result_and_policy(self) -> None:
        report = checker.summary(
            {"build": "success", "miri": "skipped"}, ["miri"]
        )
        self.assertIn("| `build` | `success` | must succeed |", report)
        self.assertIn("| `miri` | `skipped` | skip allowed |", report)


if __name__ == "__main__":
    unittest.main()
