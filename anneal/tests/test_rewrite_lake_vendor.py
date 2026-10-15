#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://opensource.org/licenses/Apache-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for rewrite-lake-vendor.py."""

from __future__ import annotations

import importlib.util
import tempfile
import subprocess
import sys
import unittest
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "rewrite-lake-vendor.py"
SPEC = importlib.util.spec_from_file_location("rewrite_lake_vendor", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
rewrite_lake_vendor = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(rewrite_lake_vendor)


def write(path: Path, contents: str = "") -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(contents, encoding="utf-8")


class RewriteLakeVendorTests(unittest.TestCase):
    def test_toml_require_rewrite_preserves_following_tables(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            lakefile = root / "lakefile.toml"
            following = ('[[lean_lib]]\nname = "Library"\n\n'
                         '[[lean_exe]]\nname = "driver"\nroot = "Main"\n'
                         '[leanOptions]\nautoImplicit = false\n')
            write(lakefile, 'name = "consumer"\n\n[[require]]\nname = "dep"\n'
                  'scope = "owner"\nrev = "main"\n\n' + following)
            self.assertTrue(rewrite_lake_vendor.replace_require_toml_blocks(
                lakefile, {"dep": root / "packages/dep"}))
            rewritten = lakefile.read_text()
            self.assertTrue(rewritten.endswith(following))
            self.assertIn('path = "packages/dep"', rewritten)
            self.assertNotIn('rev =', rewritten)
            self.assertFalse(rewrite_lake_vendor.replace_require_toml_blocks(
                lakefile, {"dep": root / "packages/dep"}))

    def test_toml_require_stops_before_single_bracket_table(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'lakefile.toml'
            following = '[leanOptions]\nautoImplicit = false\n'
            write(path, '[[require]]\nname = "dep"\nrev = "main"\n' + following)
            rewrite_lake_vendor.replace_require_toml_blocks(path, {"dep": Path(tmp) / 'dep'})
            self.assertTrue(path.read_text().endswith(following))

    def test_pinned_aesop_and_importgraph_keep_all_declared_targets(self) -> None:
        fixtures = SCRIPT.parent / "tests/fixtures/lake-vendor"
        for name, dependency in [("aesop", "batteries"), ("importGraph", "Cli")]:
            with self.subTest(package=name), tempfile.TemporaryDirectory() as tmp:
                path = Path(tmp) / "lakefile.toml"
                original = (fixtures / (name + ".toml")).read_text()
                write(path, original)
                following = original[original.index('[[lean_lib]]'):]
                self.assertTrue(rewrite_lake_vendor.replace_require_toml_blocks(
                    path, {dependency: Path(tmp) / dependency}))
                self.assertTrue(path.read_text().endswith(following))
                self.assertIn('path = "' + dependency + '"', path.read_text())

    def test_external_symlink_rejected_before_any_rewrite(self) -> None:
        for entry in [".lake", "lakefile.lean"]:
            with self.subTest(entry=entry), tempfile.TemporaryDirectory() as tmp:
                base = Path(tmp)
                root, packages, shared = base / "private", base / "packages", base / "shared"
                root.mkdir()
                packages.mkdir()
                shared.mkdir()
                original = 'require dep from git "https://example.invalid/dep" @ "rev"\n'
                write(root / "lakefile.lean", original)
                write(shared / "lakefile.lean", original)
                if entry == ".lake":
                    (root / entry).symlink_to(shared, target_is_directory=True)
                else:
                    (root / entry).unlink()
                    (root / entry).symlink_to(shared / entry)
                (packages / "dep").mkdir()
                result = subprocess.run([sys.executable, str(SCRIPT), "--root", str(root),
                                         "--packages-dir", str(packages)],
                                        capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("symlink leaves private roots", result.stderr)
                self.assertEqual((shared / "lakefile.lean").read_text(), original)
                self.assertEqual((root / "lakefile.lean").read_text(), original)

    def test_internal_payload_links_are_allowed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root, packages = Path(tmp) / "private", Path(tmp) / "packages"
            root.mkdir()
            packages.mkdir()
            write(root / "real.lean", "def value := 1\n")
            (root / "linked.lean").symlink_to("real.lean")
            rewrite_lake_vendor.validate_vendoring_roots(root, packages)

    def test_long_unmatched_trace_path_does_not_backtrack_exponentially(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root, packages = Path(tmp) / 'root', Path(tmp) / 'packages'
            root.mkdir()
            (packages / 'mathlib').mkdir(parents=True)
            unrelated = '/' + '/'.join(['longsegment'] * 80) + '/Unrelated.lean'
            trace = root / 'Module.trace'
            write(trace, unrelated + '\n/upstream/packages/mathlib/Mathlib.lean\n')
            result = subprocess.run([sys.executable, str(SCRIPT), '--root', str(root),
                                     '--packages-dir', str(packages), '--rewrite-traces'],
                                    capture_output=True, text=True, timeout=5)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(trace.read_text(), unrelated + '\nMathlib.lean\n')

    def test_rewrites_upstream_aeneas_backend_trace_prefix(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "aeneas" / "backends" / "lean"
            packages_dir = Path(tmp) / "aeneas" / "packages"
            packages_dir.mkdir(parents=True)

            trace = root / ".lake" / "build" / "lib" / "lean" / "AeneasMeta" / "Utils.trace"
            upstream_root = "/var/lib/github-runner-work/aeneas/aeneas/dist_staging/backends/lean"
            write(
                trace,
                f"""{{
  "log": [{{"message": "lean {upstream_root}/AeneasMeta/Utils.lean"}}],
  "inputs": [["{upstream_root}/AeneasMeta/Utils.lean", "cfad31626f87a3ad"]]
}}
""",
            )

            count = rewrite_lake_vendor.rewrite_trace_prefixes(
                root=root,
                packages_dir=packages_dir,
                packages={},
                extra_prefixes=[],
            )

            self.assertEqual(count, 1)
            rewritten = trace.read_text(encoding="utf-8")
            self.assertNotIn("/var/lib", rewritten)
            self.assertNotIn("backends/lean", rewritten)
            self.assertIn("AeneasMeta/Utils.lean", rewritten)


if __name__ == "__main__":
    unittest.main()
