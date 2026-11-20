# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Exercise explicit root-manifest refreshes and their failure boundaries."""

import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import update_root_manifest as manifest


SCRIPT_DIRECTORY = Path(__file__).resolve().parent
HASH_HEADER = (
    "# Copyright 2026 The Fuchsia Authors\n#\n"
    "# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0\n"
    "# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT\n"
    "# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.\n"
    "# This file may not be copied, modified, or distributed except according to\n"
    "# those terms.\n\n"
)


class ManifestTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="anneal-manifest-check-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        (self.root / "trusted").mkdir()
        self.path = self.root / "trusted/root-manifest.sha256"
        (self.root / "Cargo.toml").write_bytes(b"manifest\n")
        (self.root / "Cargo.lock").write_bytes(b"lock\n")

    def entry(self, name, ending=b"\n", mode=b"  "):
        return b"0" * 64 + mode + name.encode() + ending

    def test_preserves_header_coverage_order_mode_and_line_endings(self):
        original = (HASH_HEADER.encode() + b"# Review before accepting these hashes.\r\n"
                    + self.entry("Cargo.lock", b"\r\n", b" *")
                    + self.entry("Cargo.toml", b""))
        self.path.write_bytes(original)
        self.path.chmod(0o640)
        self.assertTrue(manifest.update(self.root))
        expected = original
        for name in ["Cargo.lock", "Cargo.toml"]:
            digest = hashlib.sha256((self.root / name).read_bytes()).hexdigest().encode()
            expected = expected.replace(b"0" * 64, digest, 1)
        self.assertEqual(self.path.read_bytes(), expected)
        self.assertEqual(self.path.stat().st_mode & 0o777, 0o640)
        self.assertFalse(manifest.update(self.root))

    def test_missing_input_leaves_original_manifest_untouched(self):
        original = self.entry("Cargo.toml") + self.entry("missing.file")
        self.path.write_bytes(original)
        with self.assertRaises(manifest.ManifestError):
            manifest.update(self.root)
        self.assertEqual(self.path.read_bytes(), original)
        self.assertEqual(sorted(p.name for p in self.path.parent.iterdir()),
                         ["root-manifest.sha256"])

    def test_invalid_empty_duplicate_and_escaping_manifest_rejected(self):
        for original in [b"# no entries\n", b"bad checksum\n",
                         self.entry("Cargo.toml") * 2, self.entry("../outside"),
                         self.entry("/absolute"), self.entry("./Cargo.toml"),
                         self.entry("trusted/root-manifest.sha256")]:
            with self.subTest(original=original):
                self.path.write_bytes(original)
                with self.assertRaises(manifest.ManifestError):
                    manifest.update(self.root)
                self.assertEqual(self.path.read_bytes(), original)

    def test_symlink_manifest_or_covered_file_rejected(self):
        (self.root / "alias.toml").symlink_to("Cargo.toml")
        self.path.write_bytes(self.entry("alias.toml"))
        with self.assertRaises(manifest.ManifestError):
            manifest.update(self.root)
        self.path.unlink()
        self.path.symlink_to("../Cargo.toml")
        with self.assertRaises(manifest.ManifestError):
            manifest.update(self.root)

    def test_manifest_parent_cannot_redirect_the_write_outside_the_root(self):
        original = self.entry("Cargo.toml")
        with tempfile.TemporaryDirectory() as outside:
            destination = Path(outside) / "root-manifest.sha256"
            destination.write_bytes(original)
            self.path.parent.rmdir()
            self.path.parent.symlink_to(outside, target_is_directory=True)
            with self.assertRaises(manifest.ManifestError):
                manifest.update(self.root)
            self.assertEqual(destination.read_bytes(), original)
            self.assertEqual(list(Path(outside).iterdir()), [destination])

    def test_failed_replacement_keeps_original_and_cleans_temporary(self):
        original = self.entry("Cargo.toml")
        self.path.write_bytes(original)
        with patch.object(manifest.os, "replace", side_effect=OSError("injected failure")):
            with self.assertRaises(OSError):
                manifest.update(self.root)
        self.assertEqual(self.path.read_bytes(), original)
        self.assertEqual(sorted(p.name for p in self.path.parent.iterdir()),
                         ["root-manifest.sha256"])

    def test_cli_reports_missing_manifest_and_explicit_refresh(self):
        command = [sys.executable, "-B", str(SCRIPT_DIRECTORY / "update_root_manifest.py"),
                   "--root", str(self.root)]
        result = subprocess.run(command, capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn("expected an existing regular manifest", result.stderr)
        self.path.write_bytes(self.entry("Cargo.toml"))
        result = subprocess.run(command, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("Updated root-manifest hashes", result.stdout)
        result = subprocess.run(command, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("hashes unchanged", result.stdout)


if __name__ == "__main__":
    unittest.main()
