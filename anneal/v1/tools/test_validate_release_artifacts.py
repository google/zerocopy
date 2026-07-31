#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for trusted Anneal release artifact validation."""

from __future__ import annotations

import contextlib
import hashlib
import importlib.util
import io
import json
import tempfile
import unittest
from pathlib import Path


TOOLS = Path(__file__).resolve().parent
TAG = "anneal-toolchains-v1.2.3-456-deadbeefcafe"
REPOSITORY = "google/zerocopy"


def load_validator():
    path = TOOLS / "validate-release-artifacts.py"
    spec = importlib.util.spec_from_file_location("validate_release_artifacts", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


validator = load_validator()


class ValidateReleaseArtifactsTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary_directory = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary_directory.name)
        self.metadata_dir = self.root / "metadata"
        self.archive_dir = self.root / "archives"
        self.metadata_dir.mkdir()
        self.archive_dir.mkdir()
        self.metadata = {}

        for target, (os_name, arch) in validator.EXPECTED_TARGETS.items():
            filename = validator.archive_filename(target)
            contents = f"archive contents for {target}\n".encode()
            (self.archive_dir / filename).write_bytes(contents)
            metadata = {
                "target": target,
                "os": os_name,
                "arch": arch,
                "filename": filename,
                "sha256": hashlib.sha256(contents).hexdigest(),
                "url": validator.release_url(REPOSITORY, TAG, filename),
            }
            self.metadata[target] = metadata
            self._write_metadata(target)

    def tearDown(self) -> None:
        self.temporary_directory.cleanup()

    def _metadata_path(self, target: str) -> Path:
        return self.metadata_dir / f"{target}.json"

    def _write_metadata(self, target: str) -> None:
        self._metadata_path(target).write_text(
            json.dumps(self.metadata[target], indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

    def _validate(self, *, with_archives: bool = True):
        return validator.validate_release_artifacts(
            metadata_dir=self.metadata_dir,
            archive_dir=self.archive_dir if with_archives else None,
            tag=TAG,
            repository=REPOSITORY,
        )

    def test_accepts_exact_metadata_and_archives(self) -> None:
        self.assertEqual(self._validate(), self.metadata)

    def test_archive_validation_is_optional(self) -> None:
        for archive in self.archive_dir.iterdir():
            archive.unlink()
        self.assertEqual(self._validate(with_archives=False), self.metadata)

    def test_metadata_directory_must_have_exact_files(self) -> None:
        target = "linux-x86_64"
        path = self._metadata_path(target)
        path.unlink()
        with self.assertRaisesRegex(validator.ValidationError, "missing linux-x86_64.json"):
            self._validate()

        self._write_metadata(target)
        (self.metadata_dir / "extra.json").write_text("{}", encoding="utf-8")
        with self.assertRaisesRegex(validator.ValidationError, "unexpected extra.json"):
            self._validate()

    def test_archive_directory_must_have_exact_files(self) -> None:
        target = "linux-x86_64"
        filename = validator.archive_filename(target)
        path = self.archive_dir / filename
        path.unlink()
        with self.assertRaisesRegex(validator.ValidationError, f"missing {filename}"):
            self._validate()

        path.write_bytes(b"archive contents for linux-x86_64\n")
        (self.archive_dir / "extra.tar.zst").write_bytes(b"extra")
        with self.assertRaisesRegex(validator.ValidationError, "unexpected extra.tar.zst"):
            self._validate()

    def test_rejects_non_object_and_inexact_json_schema(self) -> None:
        target = "linux-x86_64"
        path = self._metadata_path(target)
        cases = [
            ([], "one JSON object"),
            (
                {
                    key: value
                    for key, value in self.metadata[target].items()
                    if key != "url"
                },
                "missing url",
            ),
            ({**self.metadata[target], "size": 123}, "unexpected size"),
        ]
        for value, message in cases:
            with self.subTest(message=message):
                path.write_text(json.dumps(value), encoding="utf-8")
                with self.assertRaisesRegex(validator.ValidationError, message):
                    self._validate()

    def test_rejects_duplicate_json_keys(self) -> None:
        target = "linux-x86_64"
        metadata = self.metadata[target]
        self._metadata_path(target).write_text(
            "{"
            f'"target": {json.dumps(target)}, "target": {json.dumps(target)}, '
            + ", ".join(
                f"{json.dumps(key)}: {json.dumps(value)}"
                for key, value in metadata.items()
                if key != "target"
            )
            + "}",
            encoding="utf-8",
        )
        with self.assertRaisesRegex(validator.ValidationError, "duplicate JSON key 'target'"):
            self._validate()

    def test_all_metadata_values_must_be_strings(self) -> None:
        target = "linux-x86_64"
        for key in validator.EXPECTED_METADATA_KEYS:
            with self.subTest(key=key):
                original = self.metadata[target][key]
                self.metadata[target][key] = 1
                self._write_metadata(target)
                with self.assertRaisesRegex(
                    validator.ValidationError, f"non-string values for: {key}"
                ):
                    self._validate()
                self.metadata[target][key] = original

    def test_rejects_unreasonably_large_metadata(self) -> None:
        target = "linux-x86_64"
        with self._metadata_path(target).open("wb") as metadata:
            metadata.truncate(validator.MAX_METADATA_FILE_SIZE + 1)
        with self.assertRaisesRegex(validator.ValidationError, "maximum is 65536 bytes"):
            self._validate()

    def test_rejects_wrong_target_platform_filename_and_url(self) -> None:
        target = "linux-x86_64"
        filename = validator.archive_filename(target)
        wrong_values = {
            "target": "linux-aarch64",
            "os": "macos",
            "arch": "aarch64",
            "filename": "anneal-toolchain-linux-x86_64.zip",
            "url": validator.release_url(REPOSITORY, "another-tag", filename),
        }
        for key, wrong_value in wrong_values.items():
            with self.subTest(key=key):
                original = self.metadata[target][key]
                self.metadata[target][key] = wrong_value
                self._write_metadata(target)
                with self.assertRaisesRegex(validator.ValidationError, f"has {key}="):
                    self._validate()
                self.metadata[target][key] = original

    def test_url_must_exactly_match_repository_and_tag(self) -> None:
        target = "linux-x86_64"
        filename = validator.archive_filename(target)
        url = self.metadata[target]["url"]
        for wrong_url in (
            url.replace("google/zerocopy", "attacker/zerocopy"),
            url.replace(TAG, TAG + "-other"),
            url.replace("https://", "http://"),
            url + "?download=1",
            validator.release_url(REPOSITORY, TAG, filename + ".other"),
        ):
            with self.subTest(url=wrong_url):
                self.metadata[target]["url"] = wrong_url
                self._write_metadata(target)
                with self.assertRaisesRegex(validator.ValidationError, "has url="):
                    self._validate()
        self.metadata[target]["url"] = url

    def test_sha256_must_be_lowercase_hex(self) -> None:
        target = "linux-x86_64"
        for sha256 in ("a" * 63, "A" * 64, "g" * 64):
            with self.subTest(sha256=sha256):
                self.metadata[target]["sha256"] = sha256
                self._write_metadata(target)
                with self.assertRaisesRegex(validator.ValidationError, "64 lowercase hexadecimal"):
                    self._validate()

    def test_archive_hash_must_match_metadata(self) -> None:
        target = "linux-x86_64"
        (self.archive_dir / validator.archive_filename(target)).write_bytes(b"tampered")
        with self.assertRaisesRegex(validator.ValidationError, "has sha256"):
            self._validate()

    def test_archive_must_not_exceed_github_asset_limit(self) -> None:
        self.assertEqual(validator.GITHUB_RELEASE_ASSET_SIZE_LIMIT, 2_147_483_647)
        target = "linux-x86_64"
        path = self.archive_dir / validator.archive_filename(target)
        with path.open("wb") as archive:
            archive.truncate(validator.GITHUB_RELEASE_ASSET_SIZE_LIMIT + 1)
        with self.assertRaisesRegex(validator.ValidationError, "must not exceed 2147483647 bytes"):
            self._validate()

    def test_metadata_and_archives_must_be_regular_non_symlink_files(self) -> None:
        target = "linux-x86_64"
        metadata_path = self._metadata_path(target)
        real_metadata = self.root / "real-metadata.json"
        metadata_path.replace(real_metadata)
        metadata_path.symlink_to(real_metadata)
        with self.assertRaisesRegex(validator.ValidationError, "regular non-symlink"):
            self._validate()

        metadata_path.unlink()
        real_metadata.replace(metadata_path)
        archive_path = self.archive_dir / validator.archive_filename(target)
        real_archive = self.root / "real-archive.tar.zst"
        archive_path.replace(real_archive)
        archive_path.symlink_to(real_archive)
        with self.assertRaisesRegex(validator.ValidationError, "regular non-symlink"):
            self._validate()

    def test_directories_must_not_be_symlinks(self) -> None:
        real_metadata_dir = self.root / "real-metadata"
        self.metadata_dir.replace(real_metadata_dir)
        self.metadata_dir.symlink_to(real_metadata_dir, target_is_directory=True)
        with self.assertRaisesRegex(validator.ValidationError, "non-symlink directory"):
            self._validate()

    def test_cli_accepts_optional_archive_directory_and_reports_errors(self) -> None:
        arguments = [
            "--metadata-dir",
            str(self.metadata_dir),
            "--archive-dir",
            str(self.archive_dir),
            "--tag",
            TAG,
            "--repository",
            REPOSITORY,
        ]
        self.assertEqual(validator.main(arguments), 0)

        self.metadata["linux-x86_64"]["url"] = "https://example.com/archive"
        self._write_metadata("linux-x86_64")
        stderr = io.StringIO()
        with contextlib.redirect_stderr(stderr):
            self.assertEqual(validator.main(arguments), 1)
        self.assertIn("error:", stderr.getvalue())


if __name__ == "__main__":
    unittest.main()
