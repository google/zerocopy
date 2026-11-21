# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

from pathlib import Path
import subprocess
import tempfile
import unittest

from alpha_release import MANIFEST, UNPINNED, archive, check_archive_base, pin


class AlphaReleaseTest(unittest.TestCase):
    def setUp(self):
        self.version = "0.2.0-alpha.1"
        text = MANIFEST.read_text()
        self.text = text.replace(archive(text, self.version)[1], UNPINNED)

    def test_pins_only_the_archive_digest(self):
        updated = pin(self.text, self.version, "1" * 64)
        self.assertEqual(updated.replace("1" * 64, UNPINNED), self.text)
        self.assertEqual(archive(updated, self.version)[1], "1" * 64)
        self.assertEqual(pin(updated, self.version, "1" * 64), updated)
        with self.assertRaises(ValueError):
            pin(updated, self.version, "2" * 64)

    def test_rejects_wrong_version_and_digest(self):
        for version in ("0.2.0", "0.2.0-alpha.2", "0.1.0-alpha.1"):
            with self.subTest(version=version), self.assertRaises(ValueError):
                archive(self.text, version)
        for digest in (UNPINNED, "1", "g" * 64):
            with self.subTest(digest=digest), self.assertRaises(ValueError):
                pin(self.text, self.version, digest)

    def test_requires_the_expected_hosted_asset(self):
        alternate = self.text.replace("github.com", "example.com")
        with self.assertRaises(ValueError):
            archive(alternate, self.version)

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
            manifest = repo / "anneal/trusted/cargo-anneal/Cargo.toml"
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
