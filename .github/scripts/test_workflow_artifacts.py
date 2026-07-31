#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Regression tests for cross-workflow Actions artifact contracts."""

from __future__ import annotations

import re
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def read(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def named_step(workflow: str, name: str) -> str:
    marker = f"      - name: {name}\n"
    before, found, remainder = workflow.partition(marker)
    del before
    if not found:
        raise ValueError(f"workflow has no step named {name!r}")
    next_step = re.search(r"(?m)^      - (?:name|uses):", remainder)
    if next_step is not None:
        remainder = remainder[: next_step.start()]
    return marker + remainder


def named_job(workflow: str, name: str) -> str:
    jobs = list(
        re.finditer(r"(?m)^  (?P<name>[A-Za-z0-9_-]+):\n", workflow)
    )
    for index, match in enumerate(jobs):
        if match.group("name") != name:
            continue
        end = jobs[index + 1].start() if index + 1 < len(jobs) else None
        return workflow[match.start() : end]
    raise ValueError(f"workflow has no job named {name!r}")


class WorkflowArtifactTests(unittest.TestCase):
    def test_manual_release_artifacts_outlive_environment_approval(self) -> None:
        release = read(".github/workflows/anneal-release.yml")
        retention_name = "ANNEAL_RELEASE_ARTIFACT_RETENTION_DAYS"
        self.assertIn(f'{retention_name}: "90"', release)
        retention = f"retention-days: ${{{{ env.{retention_name} }}}}"
        expected_uploads = {
            "prepare-release-source": 1,
            "build-toolchains": 2,
            "prepare-release-pr": 1,
        }
        for job_name, expected_count in expected_uploads.items():
            with self.subTest(job=job_name):
                block = named_job(release, job_name)
                upload_count = block.count("uses: actions/upload-artifact@")
                self.assertEqual(upload_count, expected_count)
                self.assertEqual(block.count(retention), upload_count)
                self.assertEqual(
                    block.count("overwrite: true"), upload_count
                )

    def test_benchmark_survives_delayed_paired_workflow_rerun(self) -> None:
        anneal = read(".github/workflows/anneal.yml")
        uploader = read(".github/actions/upload-file-artifact/action.yml")
        docs = read(".github/workflows/docs.yml")

        producer_name = (
            "ANNEAL_BENCHMARK_ARTIFACT: "
            "anneal-ci-duration-benchmarks-${{ github.run_id }}.json"
        )
        self.assertIn(producer_name, anneal)
        upload = named_step(anneal, "Upload CI duration benchmarks")
        self.assertIn("uses: ./.github/actions/upload-file-artifact", upload)
        self.assertIn("name: ${{ env.ANNEAL_BENCHMARK_ARTIFACT }}", upload)
        self.assertIn("path: ${{ env.ANNEAL_BENCHMARK_ARTIFACT }}", upload)
        self.assertIn("retention-days: 90", upload)

        self.assertRegex(
            uploader,
            r"(?m)^  retention-days:\n"
            r"    description: .+\n"
            r"    required: false\n"
            r'    default: "1"$',
        )
        self.assertIn(
            "retention-days: ${{ inputs.retention-days }}", uploader
        )

        consumer_name = (
            "BENCHMARK_ARTIFACT: "
            "anneal-ci-duration-benchmarks-"
            "${{ needs.coordinate.outputs.anneal_run_id }}.json"
        )
        self.assertIn(consumer_name, docs)
        self.assertIn("name: ${{ env.BENCHMARK_ARTIFACT }}", docs)
        self.assertIn(
            "run-id: ${{ needs.coordinate.outputs.anneal_run_id }}", docs
        )


if __name__ == "__main__":
    unittest.main()
