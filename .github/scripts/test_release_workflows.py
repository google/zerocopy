#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Regression tests for cross-file release workflow contracts."""

import re
import tomllib
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def workflow(name: str) -> str:
    return (ROOT / ".github/workflows" / name).read_text(encoding="utf-8")


def job(contents: str, name: str) -> str:
    matches = list(re.finditer(r"^  ([A-Za-z0-9_-]+):\n", contents, re.MULTILINE))
    for index, match in enumerate(matches):
        if match.group(1) != name:
            continue
        end = matches[index + 1].start() if index + 1 < len(matches) else None
        return contents[match.start() : end]
    raise ValueError(f"workflow has no {name!r} job")


class ReleaseWorkflowTests(unittest.TestCase):
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

    def test_core_release_contract(self):
        contents = workflow("release.yml")
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
                "zerocopy-derive=zerocopy/zerocopy-derive/Cargo.toml"
            ),
            release.index("zerocopy=zerocopy/Cargo.toml"),
        )
        self.assertIn("path: release-crates", release)
        self.assertNotIn("path: zerocopy/release-crates", release)
        self.assertIn("sha: ${{ steps.source.outputs.sha }}", contents)
        self.assert_reconciled_publication(release)
        self.assertIn("core-crates-${{ needs.check-version.outputs.version }}", release)

    def test_anneal_release_contract(self):
        contents = workflow("anneal-release.yml")
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
        self.assertIn(
            "anneal-crates-${{ needs.check-version.outputs.version }}",
            release,
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

        reconciler = (
            ROOT / ".github/scripts/reconcile-crates-release.py"
        ).read_text(encoding="utf-8")
        self.assertNotIn('"--allow-dirty"', reconciler)

    def test_release_cargo_version_uses_ci_pin(self):
        action = (
            ROOT / ".github/actions/install-pinned-stable/action.yml"
        ).read_text(encoding="utf-8")
        self.assertIn("zerocopy/Cargo.toml", action)
        self.assertIn("pinned-stable", action)
        self.assertIn('rustup override set "$PINNED_STABLE"', action)
        self.assertNotIn("GITHUB_ENV", action)
        self.assertNotIn("toolchain: stable", workflow("anneal-release.yml"))


if __name__ == "__main__":
    unittest.main()
