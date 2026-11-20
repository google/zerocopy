# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Check MIR release gates and the files the release workflow can propose."""

from pathlib import Path
import unittest

from workflow_yaml import load_workflow_yaml


WORKFLOW = Path(__file__).resolve().parents[2] / ".github/workflows/release.yml"
MANIFEST = "anneal/trusted/cargo-anneal/Cargo.toml"


class ReleaseWorkflowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.workflow = load_workflow_yaml(WORKFLOW.read_text())
        cls.jobs = cls.workflow["jobs"]

    def test_mir_dispatch_requires_canonical_main(self):
        events = self.workflow["on"]
        self.assertEqual(set(events), {"push", "workflow_dispatch"})
        self.assertEqual(self.workflow["permissions"], {})
        self.assertEqual(
            set(events["workflow_dispatch"]["inputs"]["track"]["options"]),
            {"mir-prepare", "mir-publish"},
        )
        for name, track in (
            ("mir-build-archive", "mir-prepare"),
            ("mir-qualify-package", "mir-publish"),
        ):
            with self.subTest(job=name):
                self.assertEqual(
                    " ".join(self.jobs[name]["if"].split()),
                    "github.event_name == 'workflow_dispatch'"
                    f" && inputs.track == '{track}'"
                    " && github.ref == 'refs/heads/main'"
                    " && github.repository == 'google/zerocopy'",
                )

    def test_privileged_jobs_require_successful_read_only_jobs(self):
        for consumer, prerequisite, permissions in (
            ("mir-host-archive", "mir-build-archive", {"contents": "write"}),
            (
                "mir-publish-crate",
                "mir-qualify-package",
                {"contents": "read", "id-token": "write"},
            ),
        ):
            with self.subTest(job=consumer):
                job = self.jobs[consumer]
                producer = self.jobs[prerequisite]
                self.assertIn(job["needs"], (prerequisite, [prerequisite]))
                self.assertNotIn("if", job)
                self.assertEqual(job["permissions"], permissions)
                self.assertEqual(producer["permissions"], {"contents": "read"})
                for runner in (job, producer):
                    self.assertNotIn("continue-on-error", runner)
                    for step in runner["steps"]:
                        self.assertNotIn("continue-on-error", step)
                        self.assertNotIn("always(", step.get("if", ""))

    def test_publication_uses_qualified_revision_and_dedicated_environment(self):
        publisher = self.jobs["mir-publish-crate"]
        self.assertEqual(publisher["environment"], "anneal-mir-release")
        self.assertNotEqual(publisher["environment"], self.jobs["release"]["environment"])
        for name in (
            "mir-build-archive",
            "mir-host-archive",
            "mir-qualify-package",
            "mir-publish-crate",
        ):
            with self.subTest(job=name):
                [checkout] = [
                    step for step in self.jobs[name]["steps"]
                    if step.get("uses", "").startswith("actions/checkout@")
                ]
                self.assertNotIn("repository", checkout["with"])
                self.assertIn(checkout["with"].get("ref"), (None, "${{ github.sha }}"))
                self.assertEqual(checkout["with"]["persist-credentials"], "false")
        [publish] = [step["run"] for step in publisher["steps"] if "run" in step]
        self.assertEqual(publish, "cargo publish --locked -p cargo-anneal --registry crates-io")

    def test_qualification_checks_environment_and_exercises_the_packaged_cli(self):
        steps = self.jobs["mir-qualify-package"]["steps"]
        [protections, package] = [step for step in steps if "run" in step]
        self.assertNotIn("if", protections)
        self.assertNotIn("if", package)
        self.assertIn("/environments/anneal-mir-release", protections["run"])
        self.assertIn("required_reviewers", protections["run"])
        self.assertIn("deployment-branch-policies", protections["run"])
        self.assertIn("--require-pinned --archive-base", package["run"])
        self.assertIn("cargo package --locked -p cargo-anneal", package["run"])
        self.assertIn("ci/probe_alpha.py", package["run"])

    def test_archive_pin_pr_can_only_change_the_cli_manifest(self):
        [propose] = [
            step for step in self.jobs["mir-host-archive"]["steps"]
            if step.get("uses", "").startswith("peter-evans/create-pull-request@")
        ]
        self.assertEqual(propose["with"]["base"], "main")
        self.assertEqual(propose["with"]["add-paths"].splitlines(), [MANIFEST])


if __name__ == "__main__":
    unittest.main()
