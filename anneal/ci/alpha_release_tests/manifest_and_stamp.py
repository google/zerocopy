# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`alpha_release.py` tests for manifest sentinels, toolchain tags, and
manifest stamping."""

from __future__ import annotations

from .support import (
    DEV_VERSION,
    LOCK_REL,
    MANIFEST_REL,
    parse_anneal_prerelease_version,
    Path,
    release_notes,
    REPO,
    RepoFixture,
    stamp_manifests,
    tempfile,
    tomllib,
    toolchain_tag_and_url,
    UNPINNED,
)


class ManifestAndStampCases:
    """`AlphaReleaseTests` methods for manifest sentinels, toolchain tags, and
    manifest stamping."""

    def test_steady_state_repo_manifest_holds_unpinned_dev_sentinel(self) -> None:
        manifest = tomllib.loads((REPO / MANIFEST_REL).read_text(encoding="utf-8"))
        self.assertEqual(manifest["package"]["name"], "cargo-anneal")
        self.assertEqual(manifest["package"]["version"], DEV_VERSION)
        self.assertEqual(
            manifest["package"]["metadata"]["exocrate"],
            [
                {
                    "os": "linux",
                    "arch": "x86_64",
                    "sha256": UNPINNED,
                    "url": "",
                }
            ],
        )
        lock = tomllib.loads((REPO / LOCK_REL).read_text(encoding="utf-8"))
        cargo_anneal = [
            pkg for pkg in lock["package"] if pkg["name"] == "cargo-anneal"
        ]
        self.assertEqual(len(cargo_anneal), 1)
        self.assertEqual(cargo_anneal[0]["version"], DEV_VERSION)

    def test_toolchain_tag_is_disjoint_from_release_tags_and_validates_inputs(self) -> None:
        commit = "0123456789abcdef" * 2 + "01234567"
        digest = "fedcba9876543210" * 4
        tag, url = toolchain_tag_and_url(commit, digest)
        self.assertEqual(tag, "anneal-toolchain-0123456789ab-fedcba9876543210")
        self.assertEqual(
            url,
            "https://github.com/google/zerocopy/releases/download/"
            "anneal-toolchain-0123456789ab-fedcba9876543210/"
            "anneal-toolchain-linux-x86_64.tar.zst",
        )
        with self.assertRaises(ValueError):
            release_notes.parse_tag(tag)

        for bad_commit in ("", "1234", "A" * 40, "g" * 40):
            with self.subTest(bad_commit=bad_commit), self.assertRaises(ValueError):
                toolchain_tag_and_url(bad_commit, digest)
        for bad_digest in ("", UNPINNED, "1234", "F" * 64, "g" * 64):
            with self.subTest(bad_digest=bad_digest), self.assertRaises(ValueError):
                toolchain_tag_and_url(commit, bad_digest)

        for bad_version in (
            "",
            DEV_VERSION,
            "0.2.0",
            "0.2.0-alpha.0",
            "0.2.0-alpha.7+build.1",
            "0.3.0-alpha.1",
            "1.0.0-rc.1",
            "2.0.0-alpha.1",
            "1.0.0+build.1",
            "v0.2.0-alpha.7",
            "foo/v0.2.0-alpha.7",
            " 0.2.0-alpha.7",
        ):
            with self.subTest(bad_version=bad_version), self.assertRaises(
                (ValueError, SystemExit)
            ):
                parse_anneal_prerelease_version(bad_version)

    def test_stamp_preserves_ast_and_rejects_dirty_or_mismatched_checkouts(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-stamp-") as tmp:
            fx = RepoFixture(Path(tmp))
            digest = "2" * 64
            tag, url = stamp_manifests(
                fx.repo,
                version="0.2.0-alpha.7",
                commit=fx.initial_commit,
                sha256=digest,
            )
            self.assertTrue(tag.startswith("anneal-toolchain-"))
            manifest = tomllib.loads(
                (fx.repo / MANIFEST_REL).read_text(encoding="utf-8")
            )
            self.assertEqual(manifest["package"]["version"], "0.2.0-alpha.7")
            self.assertEqual(
                manifest["package"]["metadata"]["exocrate"],
                [{"os": "linux", "arch": "x86_64", "sha256": digest, "url": url}],
            )
            self.assertEqual(manifest["dependencies"], {"serde_json": "1.0"})
            lock = tomllib.loads((fx.repo / LOCK_REL).read_text(encoding="utf-8"))
            by_name = {pkg["name"]: pkg["version"] for pkg in lock["package"]}
            self.assertEqual(
                by_name,
                {"anneal-audit": "0.1.0", "cargo-anneal": "0.2.0-alpha.7"},
            )

            # Re-stamping a dirty tree fails closed.
            with self.assertRaisesRegex(ValueError, "clean checkout"):
                stamp_manifests(
                    fx.repo,
                    version="0.2.0-alpha.8",
                    commit=fx.initial_commit,
                    sha256=digest,
                )

            fx.git("checkout", "--", str(MANIFEST_REL), str(LOCK_REL))
            with self.assertRaisesRegex(ValueError, "HEAD is"):
                stamp_manifests(
                    fx.repo,
                    version="0.2.0-alpha.7",
                    commit="b" * 40,
                    sha256=digest,
                )
            with self.assertRaisesRegex(ValueError, "blocked until #4012"):
                stamp_manifests(
                    fx.repo,
                    version="0.2.0",
                    commit=fx.initial_commit,
                    sha256=digest,
                )
            (fx.repo / "untracked.txt").write_text("stray\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "clean checkout"):
                stamp_manifests(
                    fx.repo,
                    version="0.2.0-alpha.7",
                    commit=fx.initial_commit,
                    sha256=digest,
                )
