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
    main as render_main,
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
    """Copy minimal provenance inputs into `dst_root` with writable perms."""
    for rel in (
        "trusted/cargo-anneal/src/trusted_bundle.rs",
        "vendor/lean-miri/UPSTREAM_PIN.json",
        "vendor/minirust/UPSTREAM_PIN.json",
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
            minirust_upstream_pin=ANNEAL_ROOT / "vendor/minirust/UPSTREAM_PIN.json",
            correspondence_adapters_dir=ANNEAL_ROOT / "trusted/correspondence",
            correspondence_proofs_dir=ANNEAL_ROOT / "correspondence",
            trusted_lean_dir=ANNEAL_ROOT / "trusted/lean",
        )
        data = json.loads(rendered)
        self.assertEqual(
            list(data.keys()),
            [
                "schema_version",
                "upstream_repository",
                "upstream_commit",
                "upstream_lean_toolchain",
                "build_lean_toolchain",
                "upstream_pin_sha256",
                "sysroot_foundation_manifest_sha256",
                "patched_files",
                "minirust_upstream",
                "correspondence_adapters",
                "correspondence_proofs",
                "trusted_lean",
                "note",
            ],
        )
        self.assertEqual(data["schema_version"], 1)
        self.assertEqual(len(data["correspondence_adapters"]), 7)
        self.assertEqual(len(data["correspondence_proofs"]), 37)
        self.assertEqual(len(data["trusted_lean"]), 27)
        self.assertEqual(len(data["patched_files"]), 13)
        mr = data["minirust_upstream"]
        self.assertEqual(
            list(mr.keys()),
            [
                "upstream_repository",
                "upstream_commit",
                "upstream_pin_sha256",
                "tarball_sha256",
                "manifest_sha256",
                "file_count",
                "files",
            ],
        )
        self.assertEqual(mr["upstream_repository"], "https://github.com/minirust/minirust")
        self.assertEqual(
            mr["upstream_commit"], "d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed"
        )
        self.assertEqual(mr["file_count"], 30)
        self.assertEqual(len(mr["files"]), 30)
        for sha_field in ("upstream_pin_sha256", "tarball_sha256", "manifest_sha256"):
            self.assertEqual(len(mr[sha_field]), 64)
        self.assertIn("anneal-audit --require-correspondence", data["note"])
        self.assertIn("vendor/minirust/UPSTREAM_PIN.json", data["note"])
        self.assertIn("verified by Tier-0 CI and recorded here", data["note"])
        self.assertIn("unlocked Profile v2 claim definitions", data["note"])
        self.assertNotIn("against vendor/minirust/UPSTREAM_PIN.json", data["note"])
        self.assertNotIn("\\\n", data["note"])

        # CLI `--anneal-root` mode and explicit-flag mode must emit identical
        # bytes.
        with tempfile.TemporaryDirectory() as tmp:
            out_root = Path(tmp) / "root.json"
            out_explicit = Path(tmp) / "explicit.json"
            self.assertEqual(
                render_main(["--anneal-root", str(ANNEAL_ROOT), "--output", str(out_root)]),
                0,
            )
            self.assertEqual(
                render_main(
                    [
                        "--trusted-bundle-rs",
                        str(ANNEAL_ROOT / "trusted/cargo-anneal/src/trusted_bundle.rs"),
                        "--upstream-pin",
                        str(ANNEAL_ROOT / "vendor/lean-miri/UPSTREAM_PIN.json"),
                        "--minirust-upstream-pin",
                        str(ANNEAL_ROOT / "vendor/minirust/UPSTREAM_PIN.json"),
                        "--correspondence-adapters-dir",
                        str(ANNEAL_ROOT / "trusted/correspondence"),
                        "--correspondence-proofs-dir",
                        str(ANNEAL_ROOT / "correspondence"),
                        "--trusted-lean-dir",
                        str(ANNEAL_ROOT / "trusted/lean"),
                        "--output",
                        str(out_explicit),
                    ]
                ),
                0,
            )
            self.assertEqual(out_root.read_bytes(), rendered.encode("utf-8"))
            self.assertEqual(out_explicit.read_bytes(), rendered.encode("utf-8"))

    def test_rejects_untracked_lean_file_and_symlink(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            _stage_writable_anneal_fixture(ANNEAL_ROOT, root)
            mr_pin_path = root / "vendor/minirust/UPSTREAM_PIN.json"

            extra = root / "correspondence/Anneal/Extra.lean"
            extra.write_text("prelude\n")
            with self.assertRaisesRegex(ValueError, "inventory mismatch"):
                render_provenance_json(
                    trusted_bundle_rs=root / "trusted/cargo-anneal/src/trusted_bundle.rs",
                    upstream_pin=root / "vendor/lean-miri/UPSTREAM_PIN.json",
                    minirust_upstream_pin=mr_pin_path,
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
                    minirust_upstream_pin=mr_pin_path,
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
                    minirust_upstream_pin=mr_pin_path,
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
                    minirust_upstream_pin=mr_pin_path,
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
                    minirust_upstream_pin=mr_pin_path,
                    correspondence_adapters_dir=root / "trusted/correspondence",
                    correspondence_proofs_dir=root / "correspondence",
                    trusted_lean_dir=root / "trusted/lean",
                    anneal_root=root,
                )

    def test_rejects_malformed_or_tampered_minirust_upstream_pin(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            _stage_writable_anneal_fixture(ANNEAL_ROOT, root)
            pin_path = root / "vendor/lean-miri/UPSTREAM_PIN.json"
            mr_pin_path = root / "vendor/minirust/UPSTREAM_PIN.json"
            orig_mr_pin = mr_pin_path.read_text(encoding="utf-8")

            def call_render() -> str:
                return render_provenance_json(
                    trusted_bundle_rs=root / "trusted/cargo-anneal/src/trusted_bundle.rs",
                    upstream_pin=pin_path,
                    minirust_upstream_pin=mr_pin_path,
                    correspondence_adapters_dir=root / "trusted/correspondence",
                    correspondence_proofs_dir=root / "correspondence",
                    trusted_lean_dir=root / "trusted/lean",
                    anneal_root=root,
                )

            mr_pin_path.write_text('{"commit":"a","commit":"b"}', encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
                call_render()

            for mutate, pattern in (
                (lambda d: d.update(upstream_repo=""), "upstream_repo"),
                (lambda d: d.update(commit=""), "commit"),
                (lambda d: d.update(tarball_sha256="xyz"), "tarball_sha256"),
                (lambda d: d.update(manifest_sha256="0" * 63), "manifest_sha256"),
                (lambda d: d.update(file_count=True), "file_count"),
                (lambda d: d.update(file_count=29), "count mismatch"),
                (lambda d: d["files"].update({"README.md": "not-hex"}), "invalid files entry"),
            ):
                bad = json.loads(orig_mr_pin)
                mutate(bad)
                mr_pin_path.write_text(json.dumps(bad), encoding="utf-8")
                with self.assertRaisesRegex(ValueError, pattern):
                    call_render()

            mr_pin_path.write_text(orig_mr_pin, encoding="utf-8")
            outside_mr = Path(tmp) / "outside_minirust"
            outside_mr.mkdir()
            shutil.copyfile(mr_pin_path, outside_mr / "UPSTREAM_PIN.json")
            shutil.rmtree(root / "vendor/minirust")
            (root / "vendor/minirust").symlink_to(outside_mr)
            with self.assertRaisesRegex(ValueError, "regular directory"):
                call_render()

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
                        minirust_upstream_pin=root / "vendor/minirust/UPSTREAM_PIN.json",
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
