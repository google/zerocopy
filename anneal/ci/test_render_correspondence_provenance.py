#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `render_correspondence_provenance.py`."""

import json
import os
from pathlib import Path
import shutil
import stat
import tempfile
import unittest

from render_correspondence_provenance import (
    _decode_rust_string_escapes,
    render_provenance_json,
)


ANNEAL_ROOT = Path(__file__).resolve().parents[1]


def _make_tree_writable(root: Path) -> None:
    """Ensure copied fixture files and directories are owner-writable."""
    for dirpath, dirnames, filenames in os.walk(root, topdown=True, followlinks=False):
        dp = Path(dirpath)
        dp.chmod(stat.S_IMODE(dp.stat().st_mode) | stat.S_IRWXU)
        for name in filenames:
            fp = dp / name
            if not fp.is_symlink():
                fp.chmod(stat.S_IMODE(fp.stat().st_mode) | stat.S_IRUSR | stat.S_IWUSR)


def _stage_writable_anneal_fixture(src_root: Path, dst_root: Path) -> None:
    """Copy minimal provenance inputs into `dst_root` with writable permissions."""
    for rel in (
        "trusted/cargo-anneal/src/trusted_bundle.rs",
        "vendor/lean-miri/UPSTREAM_PIN.json",
    ):
        dst = dst_root / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src_root / rel, dst)
    for rel_dir in ("trusted/correspondence", "correspondence", "trusted/lean"):
        shutil.copytree(src_root / rel_dir, dst_root / rel_dir, copy_function=shutil.copyfile)
    _make_tree_writable(dst_root)


class RenderCorrespondenceProvenanceTests(unittest.TestCase):
    def test_decode_rust_string_escapes_handles_backslashes_and_continuations(self):
        # Escaped backslash immediately before a literal newline must stay a
        # literal backslash + newline, not trigger a line continuation.
        self.assertEqual(_decode_rust_string_escapes("foo\\\\\n  n"), "foo\\\n  n")
        self.assertEqual(_decode_rust_string_escapes("foo\\\\\n  bar"), "foo\\\n  bar")
        self.assertEqual(_decode_rust_string_escapes("foo\\\\\r\n  bar"), "foo\\\r\n  bar")
        # Single-line and multi-line (blank-line) Rust continuations collapse.
        self.assertEqual(_decode_rust_string_escapes("foo\\\n  bar"), "foobar")
        self.assertEqual(_decode_rust_string_escapes("foo\\\n\n  bar"), "foobar")
        self.assertEqual(_decode_rust_string_escapes("foo\\\r\n\r\n\t bar"), "foobar")
        # Bare CR after backslash is not a valid Rust continuation.
        with self.assertRaisesRegex(ValueError, "unsupported Rust string escape"):
            _decode_rust_string_escapes("foo\\\rbar")

    def test_renders_valid_schema_and_all_canonical_entries(self):
        rendered = render_provenance_json(
            trusted_bundle_rs=ANNEAL_ROOT / "trusted/cargo-anneal/src/trusted_bundle.rs",
            upstream_pin=ANNEAL_ROOT / "vendor/lean-miri/UPSTREAM_PIN.json",
            correspondence_adapters_dir=ANNEAL_ROOT / "trusted/correspondence",
            correspondence_proofs_dir=ANNEAL_ROOT / "correspondence",
            trusted_lean_dir=ANNEAL_ROOT / "trusted/lean",
        )
        data = json.loads(rendered)
        self.assertEqual(data["schema_version"], 1)
        self.assertEqual(len(data["correspondence_adapters"]), 7)
        self.assertEqual(len(data["correspondence_proofs"]), 19)
        self.assertEqual(len(data["trusted_lean"]), 21)
        self.assertEqual(len(data["patched_files"]), 13)
        self.assertIn("anneal-audit --require-correspondence", data["note"])
        self.assertNotIn("\\\n", data["note"])

    def test_rejects_untracked_lean_file_and_symlink(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            _stage_writable_anneal_fixture(ANNEAL_ROOT, root)

            extra = root / "correspondence/Anneal/Extra.lean"
            extra.write_text("prelude\n")
            with self.assertRaisesRegex(ValueError, "inventory mismatch"):
                render_provenance_json(
                    trusted_bundle_rs=root / "trusted/cargo-anneal/src/trusted_bundle.rs",
                    upstream_pin=root / "vendor/lean-miri/UPSTREAM_PIN.json",
                    correspondence_adapters_dir=root / "trusted/correspondence",
                    correspondence_proofs_dir=root / "correspondence",
                    trusted_lean_dir=root / "trusted/lean",
                )
            extra.unlink()

            outside = Path(tmp) / "outside.lean"
            outside.write_text("prelude\n")
            target = root / "trusted/correspondence/Trusted/Correspondence.lean"
            target.unlink()
            target.symlink_to(outside)
            with self.assertRaisesRegex(ValueError, "symlink"):
                render_provenance_json(
                    trusted_bundle_rs=root / "trusted/cargo-anneal/src/trusted_bundle.rs",
                    upstream_pin=root / "vendor/lean-miri/UPSTREAM_PIN.json",
                    correspondence_adapters_dir=root / "trusted/correspondence",
                    correspondence_proofs_dir=root / "correspondence",
                    trusted_lean_dir=root / "trusted/lean",
                )
            target.unlink()
            shutil.copyfile(
                ANNEAL_ROOT / "trusted/correspondence/Trusted/Correspondence.lean", target
            )

            pin_path = root / "vendor/lean-miri/UPSTREAM_PIN.json"
            orig_pin = pin_path.read_text(encoding="utf-8")
            pin_path.write_text('{"repository":"a","repository":"b"}', encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
                render_provenance_json(
                    trusted_bundle_rs=root / "trusted/cargo-anneal/src/trusted_bundle.rs",
                    upstream_pin=pin_path,
                    correspondence_adapters_dir=root / "trusted/correspondence",
                    correspondence_proofs_dir=root / "correspondence",
                    trusted_lean_dir=root / "trusted/lean",
                    anneal_root=root,
                )
            bad_pin = json.loads(orig_pin)
            bad_pin["patched_files"][0]["path"] = 123
            pin_path.write_text(json.dumps(bad_pin), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "malformed patched_files"):
                render_provenance_json(
                    trusted_bundle_rs=root / "trusted/cargo-anneal/src/trusted_bundle.rs",
                    upstream_pin=pin_path,
                    correspondence_adapters_dir=root / "trusted/correspondence",
                    correspondence_proofs_dir=root / "correspondence",
                    trusted_lean_dir=root / "trusted/lean",
                    anneal_root=root,
                )
            pin_path.write_text(orig_pin, encoding="utf-8")

            outside_vendor = Path(tmp) / "outside_vendor"
            outside_vendor.mkdir()
            shutil.copyfile(pin_path, outside_vendor / "UPSTREAM_PIN.json")
            shutil.rmtree(root / "vendor/lean-miri")
            (root / "vendor/lean-miri").symlink_to(outside_vendor)
            with self.assertRaisesRegex(ValueError, "regular directory"):
                render_provenance_json(
                    trusted_bundle_rs=root / "trusted/cargo-anneal/src/trusted_bundle.rs",
                    upstream_pin=pin_path,
                    correspondence_adapters_dir=root / "trusted/correspondence",
                    correspondence_proofs_dir=root / "correspondence",
                    trusted_lean_dir=root / "trusted/lean",
                    anneal_root=root,
                )

    def test_rejects_unreadable_subdirectory_on_walk(self):
        if os.geteuid() == 0:
            self.skipTest("chmod 0o000 does not block root traversal")
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            _stage_writable_anneal_fixture(ANNEAL_ROOT, root)

            unreadable = root / "correspondence/Anneal/Hidden"
            unreadable.mkdir(parents=True)
            unreadable.chmod(0o000)
            try:
                with self.assertRaisesRegex(ValueError, "cannot traverse directory"):
                    render_provenance_json(
                        trusted_bundle_rs=root / "trusted/cargo-anneal/src/trusted_bundle.rs",
                        upstream_pin=root / "vendor/lean-miri/UPSTREAM_PIN.json",
                        correspondence_adapters_dir=root / "trusted/correspondence",
                        correspondence_proofs_dir=root / "correspondence",
                        trusted_lean_dir=root / "trusted/lean",
                    )
            finally:
                unreadable.chmod(0o700)

    def test_fixture_staging_succeeds_from_readonly_source_tree(self):
        with tempfile.TemporaryDirectory() as tmp:
            ro_src = Path(tmp) / "ro_anneal"
            _stage_writable_anneal_fixture(ANNEAL_ROOT, ro_src)
            for dirpath, _, filenames in os.walk(ro_src, topdown=False, followlinks=False):
                dp = Path(dirpath)
                for name in filenames:
                    (dp / name).chmod(0o444)
                dp.chmod(0o555)
            try:
                dst = Path(tmp) / "writable_anneal"
                _stage_writable_anneal_fixture(ro_src, dst)
                (dst / "correspondence/Anneal/Extra.lean").write_text("prelude\n")
                (dst / "correspondence/Anneal/Hidden").mkdir(parents=True)
            finally:
                _make_tree_writable(ro_src)


if __name__ == "__main__":
    unittest.main()
