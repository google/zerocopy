# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import hashlib
from pathlib import Path
import subprocess
import tempfile
import tomllib
import unittest

from alpha_release import (
    ARCHIVE_INPUTS, LOCK_PATH, MANIFEST, MANIFEST_PATH, REPO, ROOT_HASH_PATH, UNPINNED, archive,
    archive_url, check_archive_base, pin, prepare, release_to_publish, version_to_publish,
)


class AlphaReleaseTest(unittest.TestCase):
    def setUp(self):
        text = MANIFEST.read_text()
        self.version = tomllib.loads(text)["package"]["version"]
        self.next_version = f"0.2.0-alpha.{int(self.version.rsplit('.', 1)[1]) + 1}"
        self.text = text.replace(archive(text, self.version)[1], UNPINNED)

    def test_pins_only_the_archive_digest(self):
        updated = pin(self.text, self.version, "1" * 64)
        self.assertEqual(updated.replace("1" * 64, UNPINNED), self.text)
        self.assertEqual(archive(updated, self.version)[1], "1" * 64)
        self.assertEqual(pin(updated, self.version, "1" * 64), updated)
        with self.assertRaises(ValueError):
            pin(updated, self.version, "2" * 64)

    def test_rejects_wrong_version_and_digest(self):
        for version in ("0.2.0", self.next_version, "0.1.0-alpha.1"):
            with self.subTest(version=version), self.assertRaises(ValueError):
                archive(self.text, version)
        for digest in (UNPINNED, "1", "g" * 64):
            with self.subTest(digest=digest), self.assertRaises(ValueError):
                pin(self.text, self.version, digest)

    def test_requires_the_expected_hosted_asset(self):
        alternate = self.text.replace("github.com", "example.com")
        with self.assertRaises(ValueError):
            archive(alternate, self.version)

    def test_publish_requires_a_new_version_with_a_pin_or_completion_of_a_pin(self):
        pinned = pin(self.text, self.version, "1" * 64)
        next_text = self.text.replace(self.version, self.next_version)
        next_pin = pin(next_text, self.next_version, "2" * 64)
        self.assertEqual(version_to_publish(self.text, pinned), self.version)
        self.assertEqual(version_to_publish(pinned, next_text), "")
        self.assertEqual(version_to_publish(pinned, next_pin), self.next_version)
        self.assertEqual(version_to_publish(pinned, pinned + "\n# Docs\n"), "")
        with self.assertRaisesRegex(ValueError, "already pinned"):
            version_to_publish(pinned, pin(self.text, self.version, "2" * 64))
        with self.assertRaisesRegex(ValueError, "already pinned"):
            version_to_publish(pinned, self.text)
        with self.assertRaisesRegex(ValueError, "older"):
            version_to_publish(next_pin, pinned)
        with self.assertRaisesRegex(ValueError, "older"):
            version_to_publish(next_pin, self.text)
        historical = self.text.replace("anneal-toolchain-v", "anneal-mir-toolchain-v")
        self.assertEqual(version_to_publish(historical, self.text), "")

    def test_publish_selects_the_pinning_commit_on_main(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)

            def git(*args):
                return subprocess.check_output(
                    ["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                     "-c", "commit.gpgSign=false", *args],
                    cwd=repo, text=True,
                ).strip()

            def commit(message):
                git("add", ".")
                git("commit", "--quiet", "-m", message)
                return git("rev-parse", "HEAD")

            git("init", "--quiet", "--initial-branch=main")
            manifest = repo / MANIFEST_PATH
            manifest.parent.mkdir(parents=True)
            manifest.write_text(self.text)
            before = commit("unpublished alpha")
            self.assertIsNone(release_to_publish(repo, before))

            git("switch", "--quiet", "-c", "release-pr")
            manifest.write_text(pin(self.text, self.version, "1" * 64))
            pr_head = commit("pin archive in PR")
            git("switch", "--quiet", "main")
            git("merge", "--quiet", "--no-ff", "release-pr", "-m", "merge release PR")
            release_commit = git("rev-parse", "HEAD")

            cli_source = manifest.parent / "src/main.rs"
            cli_source.parent.mkdir()
            cli_source.write_text("later CLI change\n")
            commit("change CLI after pinning")
            self.assertEqual(release_to_publish(repo, before), (self.version, release_commit))
            self.assertIsNone(release_to_publish(repo, release_commit))
            with self.assertRaisesRegex(ValueError, "first-parent history"):
                release_to_publish(repo, pr_head)

            next_text = self.text.replace(self.version, self.next_version)
            manifest.write_text(next_text)
            commit("start the next alpha without pinning")
            self.assertEqual(release_to_publish(repo, before), (self.version, release_commit))
            self.assertIsNone(release_to_publish(repo, release_commit))

            manifest.write_text(pin(next_text, self.next_version, "2" * 64))
            commit("pin a second release")
            with self.assertRaisesRegex(ValueError, "multiple Anneal releases"):
                release_to_publish(repo, before)

    def test_prepare_recreates_source_and_binds_the_release_pr_to_it(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)

            def git(*args):
                return subprocess.check_output(
                    ["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                     "-c", "commit.gpgSign=false", *args],
                    cwd=repo, text=True,
                ).strip()

            git("init", "--quiet")
            manifest = repo / MANIFEST_PATH
            lockfile = repo / LOCK_PATH
            root_hashes = repo / ROOT_HASH_PATH
            manifest.parent.mkdir(parents=True)
            manifest.write_text(self.text)
            lockfile.write_text(f'[[package]]\nname = "cargo-anneal"\nversion = "{self.version}"\n')
            root_hashes.write_text(f"{hashlib.sha256(lockfile.read_bytes()).hexdigest()}  Cargo.lock\n")
            git("add", ".")
            git("commit", "-qm", "initial alpha")
            base = git("rev-parse", "HEAD")
            self.assertEqual(git("rev-parse", f"{prepare(repo, self.version)}^{{tree}}"),
                             git("rev-parse", "HEAD^{tree}"))

            paths = [MANIFEST_PATH, LOCK_PATH, ROOT_HASH_PATH]
            source = prepare(repo, self.next_version)
            self.assertEqual(git("rev-parse", f"{source}^"), base)
            self.assertEqual(set(git("diff", "--cached", "--name-only").splitlines()), set(paths))
            with self.assertRaisesRegex(ValueError, "clean checkout"):
                prepare(repo, self.next_version)
            git("restore", "--source=HEAD", "--staged", "--worktree", "--", *paths)
            self.assertEqual(prepare(repo, self.next_version), source)
            self.assertIn(archive_url(self.next_version), manifest.read_text())
            self.assertEqual(tomllib.loads(lockfile.read_text())["package"][0]["version"],
                             self.next_version)
            self.assertIn(hashlib.sha256(lockfile.read_bytes()).hexdigest(), root_hashes.read_text())

            manifest.write_text(pin(manifest.read_text(), self.next_version, "1" * 64))
            git("add", MANIFEST_PATH)
            git("commit", "-qm", "merge release PR")
            check_archive_base(repo, source, self.next_version)
            with self.assertRaisesRegex(ValueError, "newer alpha"):
                prepare(repo, self.next_version)

    def test_pin_and_docs_can_land_without_rebuilding_the_archive(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)

            def git(*args):
                return subprocess.check_output(
                    ["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                     "-c", "commit.gpgSign=false", *args],
                    cwd=repo, text=True,
                ).strip()

            def commit(message):
                git("add", ".")
                git("commit", "--quiet", "-m", message)

            git("init", "--quiet")
            manifest = repo / MANIFEST_PATH
            manifest.parent.mkdir(parents=True)
            manifest.write_text(self.text)
            flake = repo / "anneal/flake.nix"
            flake.write_text("original archive build")
            workflow = repo / ".github/workflows/release.yml"
            workflow.parent.mkdir(parents=True)
            workflow.write_text("original release workflow")
            commit("source used for toolchain")
            source = git("rev-parse", "HEAD")

            manifest.write_text(pin(self.text, self.version, "1" * 64))
            (repo / "anneal/README.md").write_text("unrelated docs")
            commit("pin toolchain and update docs")
            check_archive_base(repo, source, self.version)

            for path in (flake, workflow):
                relative = path.relative_to(repo).as_posix()
                with self.subTest(path=relative):
                    path.write_text("changed archive build")
                    commit(f"modify {relative}")
                    with self.assertRaisesRegex(ValueError, "archive inputs changed") as failure:
                        check_archive_base(repo, source, self.version)
                    self.assertIn(relative, str(failure.exception).splitlines())
                    git("revert", "--no-edit", "HEAD")

    def test_archive_inputs_exist_and_include_prebuild_script(self):
        for rel in ARCHIVE_INPUTS:
            with self.subTest(path=rel):
                self.assertTrue((REPO / rel).exists(), rel)
        self.assertIn("anneal/ci/prebuild_bundled_oleans.py", ARCHIVE_INPUTS)
        self.assertIn("anneal/ci/render_correspondence_provenance.py", ARCHIVE_INPUTS)
        self.assertNotIn("anneal/trusted/cargo-anneal/src/bundle.rs", ARCHIVE_INPUTS)
        self.assertNotIn("anneal/trusted/cargo-anneal/src/bundled_resources.rs", ARCHIVE_INPUTS)
