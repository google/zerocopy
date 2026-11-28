# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Release workflow triggers, job graph, permissions, and checkout wiring."""

from __future__ import annotations

from .support import (
    ANNEAL_JOBS,
    DOWNLOAD_ACTION,
    SHA_PINNED_ACTION_RE,
    STRIPPED_OIDC_VARS,
    STRIPPED_RUNTIME_VARS,
    UPLOAD_ACTION,
)


class WorkflowStructureCases:
    """Workflow structure tests of `ReleaseWorkflowTests`."""

    def test_zerocopy_coexistence_and_shared_manual_entry_point(self) -> None:
        events = self.workflow["on"]
        self.assertEqual(set(events), {"push", "workflow_dispatch"})
        self.assertEqual(self.workflow["permissions"], {})
        self.assertEqual(events["push"]["branches"], ["main"])
        self.assertEqual(
            events["push"]["paths"],
            ["zerocopy/Cargo.toml", "zerocopy/zerocopy-derive/Cargo.toml"],
        )
        self.assertNotIn("check-anneal-release", self.jobs)

        inputs = events["workflow_dispatch"]["inputs"]
        self.assertEqual(inputs["project"]["options"], ["zerocopy", "anneal"])
        self.assertEqual(inputs["project"]["default"], "zerocopy")
        self.assertEqual(inputs["branch"]["default"], "main")
        self.assertEqual(inputs["commit"]["required"], "false")
        self.assertEqual(inputs["commit"]["default"], "")

        self.assertEqual(
            set(self.preparation["on"]), {"workflow_dispatch", "workflow_call"}
        )
        zerocopy = self.jobs["prepare-zerocopy"]
        self.assertEqual(
            zerocopy["uses"], "./.github/workflows/release-crate-version.yml"
        )
        self.assertEqual(zerocopy["with"]["version"], "${{ inputs.version }}")
        self.assertEqual(
            set(zerocopy["secrets"]), {"GOOGLE_PR_CREATION_BOT_TOKEN"}
        )

        caller = self.jobs["anneal-build-archive"]
        self.assertNotIn("secrets", caller)
        self.assertEqual(caller["permissions"], {"contents": "read"})
        self.assertEqual(
            " ".join(caller["if"].split()),
            "github.event_name == 'workflow_dispatch' && inputs.project == 'anneal'"
            " && github.repository == 'google/zerocopy'",
        )

    def test_five_job_dag_permissions_and_environment_isolation(self) -> None:
        expected_permissions = {
            "anneal-build-archive": {"contents": "read"},
            "anneal-host-archive": {"contents": "write"},
            "anneal-qualify-package": {"contents": "read"},
            "anneal-publish-crate": {"contents": "read", "id-token": "write"},
            "anneal-publish-github": {
                "contents": "write",
                "issues": "read",
                "pull-requests": "read",
            },
        }
        expected_needs = {
            "anneal-host-archive": "anneal-build-archive",
            "anneal-qualify-package": [
                "anneal-build-archive",
                "anneal-host-archive",
            ],
            "anneal-publish-crate": "anneal-qualify-package",
            "anneal-publish-github": [
                "anneal-qualify-package",
                "anneal-publish-crate",
            ],
        }
        for name in ANNEAL_JOBS:
            with self.subTest(job=name):
                job = self.jobs[name]
                self.assertEqual(job["runs-on"], "ubuntu-24.04")
                self.assertEqual(job["permissions"], expected_permissions[name])
                self.assertNotIn("secrets", job)
                self.assertNotIn("continue-on-error", job)
                if name != "anneal-build-archive":
                    self.assertNotIn("if", job)
                    self.assertEqual(job["needs"], expected_needs[name])
                if name == "anneal-publish-crate":
                    self.assertEqual(job["environment"], "anneal-release")
                    self.assertNotEqual(
                        job["environment"], self.jobs["release"]["environment"]
                    )
                    self.assertEqual(
                        job["concurrency"],
                        {
                            "group": "anneal-publish",
                            "cancel-in-progress": "false",
                        },
                    )
                else:
                    self.assertNotIn("environment", job)
                for step in job["steps"]:
                    self.assertNotIn("continue-on-error", step)
                    self.assertNotIn("always(", step.get("if", ""))
                    uses = step.get("uses", "")
                    self.assertFalse(
                        uses.startswith("peter-evans/create-pull-request"),
                        f"unexpected PR bot action in {name}: {uses}",
                    )

    def test_zero_expression_interpolation_in_run_and_sha_pinned_actions(self) -> None:
        for job_name, job in self.jobs.items():
            for step in job.get("steps", []):
                with self.subTest(job=job_name, step=step.get("name", step.get("uses"))):
                    if "run" in step:
                        self.assertNotIn(
                            "${{",
                            step["run"],
                            f"{job_name} interpolates GitHub expression inside run:",
                        )
                        if job_name in ANNEAL_JOBS:
                            self.assertNotRegex(
                                step["run"],
                                r"\|\s*grep\b",
                                f"{job_name} pipes into grep under pipefail (SIGPIPE hazard)",
                            )
                    if "uses" in step:
                        uses = step["uses"]
                        if uses.startswith("./"):
                            self.assertTrue(uses.startswith("./.github/"))
                        else:
                            self.assertRegex(uses, SHA_PINNED_ACTION_RE)

    def test_checkouts_fetch_depth_artifact_id_wiring_and_token_stripping(self) -> None:
        for name in ANNEAL_JOBS:
            with self.subTest(job=name):
                job = self.jobs[name]
                [checkout] = [
                    step
                    for step in job["steps"]
                    if step.get("uses", "").startswith("actions/checkout@")
                ]
                self.assertNotIn("repository", checkout["with"])
                # Every Anneal job checks out the dispatched workflow revision
                # (`github.sha`) into `$GITHUB_WORKSPACE` so composite actions
                # and workflow-coupled scripts execute at `github.sha` rather
                # than a historical target commit `C`.
                self.assertEqual(
                    checkout["with"].get("ref"), "${{ github.sha }}"
                )
                self.assertEqual(
                    checkout["with"]["persist-credentials"], "false"
                )
                self.assertEqual(checkout["with"].get("fetch-depth"), "0")
                for step in job["steps"]:
                    if "run" in step:
                        self.assertNotRegex(
                            step["run"],
                            r"(?m)^\s*git checkout\b",
                            f"{name} mutates $GITHUB_WORKSPACE HEAD via git checkout",
                        )

        # Verify immutable numeric `artifact_id` wiring between Jobs 1 and 2,
        # and zero `download-artifact` steps in Jobs 3, 4, and 5.
        build_job = self.jobs["anneal-build-archive"]
        self.assertEqual(
            build_job["outputs"]["artifact_id"],
            "${{ steps.upload.outputs.artifact-id }}",
        )
        [upload_step] = [
            s for s in build_job["steps"] if s.get("uses") == UPLOAD_ACTION
        ]
        self.assertEqual(upload_step["id"], "upload")
        self.assertEqual(
            upload_step["with"]["name"], "anneal-toolchain-linux-x86_64.tar.zst"
        )

        host_job = self.jobs["anneal-host-archive"]
        [download_step] = [
            s for s in host_job["steps"] if s.get("uses") == DOWNLOAD_ACTION
        ]
        self.assertEqual(
            download_step["with"]["artifact-id"],
            "${{ needs.anneal-build-archive.outputs.artifact_id }}",
        )
        self.assertEqual(
            download_step["with"]["expected-file"],
            "anneal-toolchain-linux-x86_64.tar.zst",
        )

        for downstream in (
            "anneal-qualify-package",
            "anneal-publish-crate",
            "anneal-publish-github",
        ):
            for step in self.jobs[downstream]["steps"]:
                uses = step.get("uses", "")
                self.assertNotIn("download-artifact", uses)

        # Verify runtime/cache token stripping after checkout on every Anneal
        # job, plus OIDC request token stripping on every `run:` step in Job 4.
        for name in ANNEAL_JOBS:
            job = self.jobs[name]
            job_env = job.get("env", {})
            steps = job["steps"]
            checkout_idx = next(
                i
                for i, s in enumerate(steps)
                if s.get("uses", "").startswith("actions/checkout@")
            )
            for step in steps[checkout_idx + 1 :]:
                if "run" not in step:
                    continue
                if step.get("id") == "emit":
                    continue
                merged_env = {**job_env, **step.get("env", {})}
                for var in STRIPPED_RUNTIME_VARS:
                    self.assertEqual(
                        merged_env.get(var),
                        "",
                        f"{name}/{step.get('name')!r} must strip {var}",
                    )
                if name == "anneal-publish-crate":
                    for oidc_var in STRIPPED_OIDC_VARS:
                        self.assertEqual(
                            merged_env.get(oidc_var),
                            "",
                            f"{name}/{step.get('name')!r} must strip {oidc_var}",
                        )
                # `alpha_release.py` steps must never receive `GH_TOKEN`.
                if "alpha_release.py" in step["run"]:
                    self.assertNotIn("GH_TOKEN", merged_env)
