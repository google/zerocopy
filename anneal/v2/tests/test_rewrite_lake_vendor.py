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
    def test_toml_rewrite_preserves_following_array_tables(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            packages_dir = root / "packages"
            batteries = packages_dir / "batteries"
            batteries.mkdir(parents=True)
            lakefile = root / "aesop" / "lakefile.toml"
            write(
                lakefile,
                """name = "aesop"

[[require]]
name = "batteries"
scope = "leanprover-community"
rev = "v4.30.0-rc2"

[[lean_lib]]
name = "Aesop"

[[lean_lib]]
name = "AesopTest"
globs = ["AesopTest.+"]
""",
            )

            changed = rewrite_lake_vendor.replace_require_toml_blocks(
                lakefile, {"batteries": batteries}
            )

            self.assertTrue(changed)
            rewritten = lakefile.read_text(encoding="utf-8")
            self.assertIn('path = "../packages/batteries"', rewritten)
            self.assertNotIn("scope =", rewritten)
            self.assertNotIn("rev =", rewritten)
            self.assertEqual(rewritten.count("[[lean_lib]]"), 2)
            self.assertIn('name = "Aesop"', rewritten)
            self.assertIn('name = "AesopTest"', rewritten)

    def test_toml_rewrite_preserves_following_regular_table(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            batteries = root / "packages" / "batteries"
            batteries.mkdir(parents=True)
            lakefile = root / "aesop" / "lakefile.toml"
            write(
                lakefile,
                """[[require]]
name = "batteries"
scope = "leanprover-community"

[leanOptions]
pp.unicode.fun = true
""",
            )

            changed = rewrite_lake_vendor.replace_require_toml_blocks(
                lakefile, {"batteries": batteries}
            )

            self.assertTrue(changed)
            rewritten = lakefile.read_text(encoding="utf-8")
            self.assertIn("[leanOptions]", rewritten)
            self.assertIn("pp.unicode.fun = true", rewritten)

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

    def test_rewrites_external_lean_and_proofwidgets_prefixes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "aeneas" / "backends" / "lean"
            packages_dir = Path(tmp) / "aeneas" / "packages"
            proofwidgets = packages_dir / "proofwidgets"
            trace = proofwidgets / "widget" / "js" / "lake.trace"
            write(
                trace,
                """{
  "log": [{"message": "/Users/wjn/ProofWidgets4/widget> npm run build"}],
  "inputs": [["/Users/wjn/ProofWidgets4/widget/src", "1234"]],
  "lean": "/var/lib/runner/.elan/toolchains/lean4/bin/lean File.lean"
}
""",
            )

            count = rewrite_lake_vendor.rewrite_trace_prefixes(
                root=root,
                packages_dir=packages_dir,
                packages={"proofwidgets": proofwidgets},
                extra_prefixes=[],
            )

            self.assertEqual(count, 1)
            rewritten = trace.read_text(encoding="utf-8")
            self.assertNotIn("/Users/wjn", rewritten)
            self.assertNotIn("/var/lib", rewritten)
            self.assertIn("widget/src", rewritten)
            self.assertIn("lean/bin/lean File.lean", rewritten)


if __name__ == "__main__":
    unittest.main()
