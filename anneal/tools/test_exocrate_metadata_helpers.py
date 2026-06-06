#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for Anneal exocrate metadata helper scripts."""

from __future__ import annotations

import hashlib
import importlib.util
import tempfile
import unittest
from pathlib import Path


TOOLS = Path(__file__).resolve().parent


def load_script(name: str):
    spec = importlib.util.spec_from_file_location(name.replace("-", "_"), TOOLS / f"{name}.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


collect_metadata = load_script("collect-release-archive-metadata")
update_metadata = load_script("update-exocrate-metadata")


def exocrate_section(os_name: str, arch: str, sha256: str, url: str) -> str:
    return f"""[package.metadata.exocrate.{os_name}.{arch}]
sha256 = "{sha256}"
url = "{url}"
"""


class ExocrateMetadataHelperTests(unittest.TestCase):
    def test_collect_archive_metadata_hashes_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            archive = Path(tmp) / "archive.tar.zst"
            archive.write_bytes(b"archive contents")

            self.assertEqual(
                collect_metadata.sha256_file(archive),
                hashlib.sha256(b"archive contents").hexdigest(),
            )

    def test_update_manifest_requires_complete_platform_metadata(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            cargo_toml = root / "Cargo.toml"
            original_sha = "0" * 64
            cargo_toml.write_text(
                "[package]\nname = \"cargo-anneal\"\n\n"
                + "".join(
                    exocrate_section(os_name, arch, original_sha, f"https://example.com/{os_name}-{arch}.tar.zst")
                    for os_name, arch in sorted(update_metadata.EXPECTED_PLATFORMS)
                ),
                encoding="utf-8",
            )

            metadata = {
                platform: {
                    "sha256": f"{i + 1:064x}",
                    "url": f"https://github.com/google/zerocopy/releases/download/tag/{target}.tar.zst",
                }
                for i, (platform, target) in enumerate(sorted(update_metadata.EXPECTED_TARGETS.items()))
            }
            update_metadata.update_manifest(cargo_toml, metadata)
            updated = cargo_toml.read_text(encoding="utf-8")

            for platform, values in metadata.items():
                os_name, arch = platform
                self.assertIn(f"[package.metadata.exocrate.{os_name}.{arch}]", updated)
                self.assertIn(f'sha256 = "{values["sha256"]}"', updated)
                self.assertIn(f'url = "{values["url"]}"', updated)
            self.assertNotIn(original_sha, updated)

    def test_load_metadata_rejects_wrong_target_duplicate_and_wrong_tag(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            linux = root / "linux.json"
            linux.write_text(
                """{
  "target": "linux-x86_64",
  "os": "linux",
  "arch": "x86_64",
  "sha256": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
  "url": "https://github.com/google/zerocopy/releases/download/tag/archive.tar.zst"
}
""",
                encoding="utf-8",
            )
            duplicate = root / "duplicate.json"
            duplicate.write_text(linux.read_text(encoding="utf-8"), encoding="utf-8")
            wrong_target = root / "wrong-target.json"
            wrong_target.write_text(
                linux.read_text(encoding="utf-8").replace("linux-x86_64", "macos-x86_64"),
                encoding="utf-8",
            )
            wrong_tag = root / "wrong-tag.json"
            wrong_tag.write_text(
                linux.read_text(encoding="utf-8").replace("/tag/", "/other-tag/"),
                encoding="utf-8",
            )

            self.assertEqual(
                update_metadata.load_metadata([linux], expected_release_tag="tag"),
                {
                    ("linux", "x86_64"): {
                        "sha256": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                        "url": "https://github.com/google/zerocopy/releases/download/tag/archive.tar.zst",
                    }
                },
            )
            with self.assertRaises(SystemExit):
                update_metadata.load_metadata([linux, duplicate], expected_release_tag="tag")
            with self.assertRaises(SystemExit):
                update_metadata.load_metadata([wrong_target], expected_release_tag="tag")
            with self.assertRaises(SystemExit):
                update_metadata.load_metadata([wrong_tag], expected_release_tag="tag")


if __name__ == "__main__":
    unittest.main()
