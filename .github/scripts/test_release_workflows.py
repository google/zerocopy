#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Regression tests for cross-file release workflow contracts."""

import json
import os
import re
import subprocess
import tempfile
import tomllib
import unittest
from typing import Any
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
YQ = os.environ.get("YQ", "yq")


def workflow(name: str) -> str:
    return (ROOT / ".github/workflows" / name).read_text(encoding="utf-8")


def workflow_object(name: str) -> dict[str, Any]:
    """Decodes a workflow with the parser pinned by check_actions.sh."""

    path = ROOT / ".github/workflows" / name
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


def job(contents: str, name: str) -> str:
    matches = list(re.finditer(r"^  ([A-Za-z0-9_-]+):\n", contents, re.MULTILINE))
    for index, match in enumerate(matches):
        if match.group(1) != name:
            continue
        end = matches[index + 1].start() if index + 1 < len(matches) else None
        return contents[match.start() : end]
    raise ValueError(f"workflow has no {name!r} job")


class ReleaseWorkflowTests(unittest.TestCase):
    def assert_trusted_historical_checkouts(
        self,
        release_job: dict[str, Any],
        source_ref: str,
        *,
        full_history: bool = False,
    ):
        """Binds trusted tooling and historical source to distinct checkouts."""

        checkouts = [
            step
            for step in release_job["steps"]
            if str(step.get("uses", "")).startswith("actions/checkout@")
        ]
        self.assertEqual(len(checkouts), 2)
        trusted, source = checkouts
        self.assertEqual(trusted["with"]["ref"], "${{ github.workflow_sha }}")
        self.assertNotIn("path", trusted["with"])
        self.assertEqual(source["with"]["ref"], source_ref)
        self.assertEqual(source["with"]["path"], "release-source")
        for checkout in checkouts:
            self.assertIs(checkout["with"]["persist-credentials"], False)
            if full_history:
                self.assertEqual(checkout["with"]["fetch-depth"], 0)

    def assert_unprivileged_preparation(self, block: str, script: str):
        self.assertIn(script, block)
        self.assertNotIn("create-crates-release-plan.py", block)
        self.assertNotIn("contents: write", block)
        self.assertNotIn("id-token: write", block)
        self.assertNotIn("CARGO_REGISTRY_TOKEN", block)

    def assert_reconciled_publication(self, block: str):
        self.assertIn("environment: release", block)
        self.assertIn("id-token: write", block)
        self.assertIn("create-crates-release-plan.py", block)
        self.assertIn("reconcile-crates-release.py", block)
        self.assertNotIn("cargo publish", block)
        self.assertNotIn("git tag", block)
        self.assertLess(
            block.index("create-crates-release-plan.py"),
            block.index("crates-io-auth-action"),
        )

    def assert_artifact_contract(
        self,
        prepare: dict[str, Any],
        release: dict[str, Any],
        artifact_name: str,
        concurrency_group: str,
        upload_path: str = "release-crates/*.crate",
        download_path: str = "release-crates",
    ):
        # Bind each side to the action which implements it. A raw text search
        # could pass from a stale comment, a second artifact, or the unrelated
        # concurrency key even if the actual upload/download names drifted
        # apart and a privileged release would fail only after approval.
        uploads = [
            step
            for step in prepare["steps"]
            if str(step.get("uses", "")).startswith(
                "actions/upload-artifact@"
            )
        ]
        downloads = [
            step
            for step in release["steps"]
            if str(step.get("uses", "")).startswith(
                "actions/download-artifact@"
            )
        ]
        self.assertEqual(len(uploads), 1)
        self.assertEqual(len(downloads), 1)
        self.assertEqual(uploads[0]["with"]["name"], artifact_name)
        self.assertEqual(downloads[0]["with"]["name"], artifact_name)
        self.assertEqual(uploads[0]["with"]["path"], upload_path)
        self.assertEqual(downloads[0]["with"]["path"], download_path)
        self.assertEqual(
            release["concurrency"]["group"],
            concurrency_group,
        )

    def test_core_release_contract(self):
        contents = workflow("release.yml")
        parsed_jobs = workflow_object("release.yml")["jobs"]
        self.assertIn("github.event.before", contents)
        self.assertNotIn("git checkout -q HEAD^", contents)
        prepare = job(contents, "prepare-release")
        release = job(contents, "release")
        self.assert_unprivileged_preparation(
            prepare,
            "ci/package_release_crates.sh",
        )
        self.assertIn("retention-days: 90", prepare)
        self.assertIn("overwrite: true", prepare)
        self.assertLess(
            release.index(
                "zerocopy-derive=release-source/zerocopy/"
                "zerocopy-derive/Cargo.toml"
            ),
            release.index(
                "zerocopy=release-source/zerocopy/Cargo.toml"
            ),
        )
        self.assertIn("path: release-crates", release)
        self.assertNotIn("path: release-source/release-crates", release)
        self.assertIn("sha: ${{ steps.source.outputs.sha }}", contents)
        self.assert_reconciled_publication(release)
        self.assert_trusted_historical_checkouts(
            parsed_jobs["check-version"],
            "${{ github.event.inputs.sha || github.sha }}",
            full_history=True,
        )
        for job_name in ("prepare-release", "release"):
            self.assert_trusted_historical_checkouts(
                parsed_jobs[job_name],
                "${{ needs.check-version.outputs.sha }}",
            )
        self.assertIn(
            "python3 ../.github/scripts/check-crate-version-change.py",
            parsed_jobs["check-version"]["steps"][-1]["run"],
        )
        self.assertIn(
            "--source-root \"$GITHUB_WORKSPACE/release-source/zerocopy\"",
            prepare,
        )
        self.assertIn(
            "--cargo-command ci/run_cargo_for_release.sh",
            release,
        )
        # Option-like command arguments must use argparse's `--option=value`
        # spelling. With a separating space, the plan CLI interprets each
        # value as a new unknown option instead of part of the command prefix.
        self.assertIn("--cargo-command=--prebuilt", release)
        self.assertIn("--cargo-command=--source-root", release)
        self.assertIn(
            "--cargo-command release-source/zerocopy",
            release,
        )
        self.assertNotIn(
            "--cargo-command release-source/zerocopy/cargo.sh",
            release,
        )
        self.assertIn(
            "zerocopy-derive=release-source/zerocopy/zerocopy-derive/Cargo.toml",
            release,
        )
        self.assertIn(
            "zerocopy=release-source/zerocopy/Cargo.toml",
            release,
        )
        self.assert_artifact_contract(
            parsed_jobs["prepare-release"],
            parsed_jobs["release"],
            "core-crates-${{ needs.check-version.outputs.sha }}",
            "core-crates-${{ needs.check-version.outputs.version }}",
        )

    def test_anneal_release_contract(self):
        contents = workflow("anneal-release.yml")
        parsed_jobs = workflow_object("anneal-release.yml")["jobs"]
        self.assertIn("github.event.before", contents)
        self.assertNotIn("git checkout -q HEAD^", contents)
        self.assertNotIn("tools/pre-publish.sh", contents)
        prepare = job(contents, "prepare-crates-release")
        release = job(contents, "release")
        self.assert_unprivileged_preparation(
            prepare,
            "anneal/v1/tools/package-release-crates.sh",
        )
        self.assertIn(
            "retention-days: "
            "${{ env.ANNEAL_RELEASE_ARTIFACT_RETENTION_DAYS }}",
            prepare,
        )
        self.assertIn("overwrite: true", prepare)
        self.assertLess(
            release.index("exocrate=exocrate/Cargo.toml"),
            release.index("cargo-anneal=anneal/v1/Cargo.toml"),
        )
        self.assert_reconciled_publication(release)
        self.assert_artifact_contract(
            parsed_jobs["prepare-crates-release"],
            parsed_jobs["release"],
            "anneal-crates-${{ github.sha }}",
            "anneal-crates-${{ needs.check-version.outputs.version }}",
        )
        pinned_action = "uses: ./.github/actions/install-pinned-stable"
        self.assertIn(pinned_action, prepare)
        self.assertIn(pinned_action, release)

    def test_anneal_dependency_matches_publishable_exocrate(self):
        anneal_v1 = tomllib.loads(
            (ROOT / "anneal/v1/Cargo.toml").read_text(encoding="utf-8")
        )
        anneal_v2 = tomllib.loads(
            (ROOT / "anneal/Cargo.toml").read_text(encoding="utf-8")
        )
        exocrate = tomllib.loads(
            (ROOT / "exocrate/Cargo.toml").read_text(encoding="utf-8")
        )
        version = exocrate["package"]["version"]
        for manifest, expected_path in (
            (anneal_v1, "../../exocrate"),
            (anneal_v2, "../exocrate"),
        ):
            dependency = manifest["dependencies"]["exocrate"]
            self.assertEqual(dependency["path"], expected_path)
            self.assertEqual(dependency["version"], f"={version}")

        for lock_path in (
            "exocrate/Cargo.lock",
            "anneal/Cargo.lock",
            "anneal/v1/Cargo.lock",
        ):
            lock = tomllib.loads(
                (ROOT / lock_path).read_text(encoding="utf-8")
            )
            locked = [
                package["version"]
                for package in lock["package"]
                if package["name"] == "exocrate"
            ]
            self.assertEqual(locked, [version], lock_path)
        for field in ("description", "license", "repository"):
            self.assertIn(field, exocrate["package"])

    def test_pr_packaging_scripts_are_strict(self):
        for path in (
            "zerocopy/ci/package_release_crates.sh",
            "anneal/v1/tools/package-release-crates.sh",
        ):
            contents = (ROOT / path).read_text(encoding="utf-8")
            self.assertIn("--locked", contents)
            self.assertNotIn("--allow-dirty", contents)
            # Cargo uses this option to prepare packaged lockfiles on the
            # assumption that local interdependent crates will be published to
            # the named registry. Dropping it can make a locked consumer
            # archive unusable even though local patch-based verification
            # continues to pass.
            commands = "\n".join(
                line
                for line in contents.splitlines()
                if not line.lstrip().startswith("#")
            )
            self.assertEqual(commands.count("--registry crates-io"), 4)

        reconciler = (
            ROOT / ".github/scripts/reconcile-crates-release.py"
        ).read_text(encoding="utf-8")
        self.assertNotIn('"--allow-dirty"', reconciler)

    def test_trusted_cargo_driver_accepts_separate_source_root(self):
        # The historical source supplies only toolchain metadata. It does not
        # need to contain (and must not execute) a Cargo wrapper of its own.
        with tempfile.TemporaryDirectory() as temporary:
            source_root = Path(temporary) / "historical source" / "zerocopy"
            source_root.mkdir(parents=True)
            (source_root / "Cargo.toml").write_text(
                """[package]
name = "historical-source"
version = "1.0.0"
rust-version = "1.56.0"

[package.metadata.build-rs]
test-nightly = "nightly-2026-01-25"

[package.metadata.ci]
pinned-stable = "1.93.1"
pinned-nightly = "nightly-2026-01-25"
""",
                encoding="utf-8",
            )
            marker = Path(temporary) / "historical-cargo-ran"
            cargo = source_root / "cargo.sh"
            cargo.write_text(
                """#!/usr/bin/env bash
touch "$HISTORICAL_CARGO_MARKER"
exit 99
""",
                encoding="utf-8",
            )
            cargo.chmod(0o755)
            environment = dict(
                os.environ,
                HISTORICAL_CARGO_MARKER=str(marker),
            )

            result = subprocess.run(
                [
                    ROOT / "ci/run_cargo_for_release.sh",
                    "--source-root",
                    source_root,
                    "--version",
                    "stable",
                ],
                check=True,
                capture_output=True,
                env=environment,
                text=True,
            )

            self.assertEqual(result.stdout.strip(), "1.93.1")
            self.assertFalse(marker.exists())

    def test_release_cargo_version_uses_ci_pin(self):
        action = (
            ROOT / ".github/actions/install-pinned-stable/action.yml"
        ).read_text(encoding="utf-8")
        self.assertIn("zerocopy/Cargo.toml", action)
        self.assertIn("pinned-stable", action)
        self.assertIn('rustup override set "$PINNED_STABLE"', action)
        self.assertNotIn("GITHUB_ENV", action)
        pinned_action = "./.github/actions/install-pinned-stable"
        for workflow_name, job_names in (
            (
                "anneal-release.yml",
                ("prepare-crates-release", "release"),
            ),
            ("anneal.yml", ("check_publishable",)),
        ):
            # Keep the PR check coordinated with both sides of the release
            # artifact boundary. Inspect the decoded jobs rather than merely
            # finding the action name somewhere in each workflow.
            jobs = workflow_object(workflow_name)["jobs"]
            for job_name in job_names:
                uses = [
                    step.get("uses")
                    for step in jobs[job_name]["steps"]
                    if "uses" in step
                ]
                self.assertEqual(uses.count(pinned_action), 1)
                self.assertFalse(
                    any(
                        str(action).startswith("dtolnay/rust-toolchain@")
                        for action in uses
                    )
                )


if __name__ == "__main__":
    unittest.main()
