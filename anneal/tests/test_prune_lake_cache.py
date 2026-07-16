#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for prune-lake-cache.py."""

from __future__ import annotations

import importlib.util
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "prune-lake-cache.py"
SPEC = importlib.util.spec_from_file_location("prune_lake_cache", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
prune_lake_cache = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(prune_lake_cache)


def write(path: Path, contents: str = "") -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(contents, encoding="utf-8")


class PruneLakeCacheTests(unittest.TestCase):
    def test_prunes_mathlib_to_reachable_closure(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            project_root = Path(tmp) / "project"
            packages_root = project_root / ".lake" / "packages"
            mathlib = packages_root / "mathlib"

            write(project_root / "Main.lean", "import Mathlib.Data.Nat.Basic\n")
            write(
                project_root / ".lake" / "build" / "lib" / "lean" / "Main.trace",
                '{"deps": ["Mathlib.Tactic.Linarith"]}',
            )
            write(project_root / ".lake" / "build" / "lib" / "lean" / "Mathlib.olean")
            write(project_root / ".lake" / "build" / "lib" / "lean" / "Mathlib" / "Init.olean")

            write(mathlib / "Mathlib" / "Data" / "Nat" / "Basic.lean", "import Mathlib.Init.Zero\n")
            write(mathlib / "Mathlib" / "Init" / "Zero.lean")
            write(mathlib / "Mathlib" / "Tactic" / "Linarith.lean", "import Mathlib.Init.Zero\n")
            write(mathlib / "Mathlib" / "Unused.lean", "import Mathlib.Init.Zero\n")
            write(mathlib / "lakefile.lean", "import Lake\n")
            write(mathlib / "README.md", "unused package metadata\n")
            write(mathlib / ".github" / "workflows" / "ci.yml", "name: unused\n")
            write(mathlib / "Mathlib" / "Unused.ltar", "unused source archive\n")

            for module in [
                "Mathlib/Data/Nat/Basic",
                "Mathlib/Init/Zero",
                "Mathlib/Tactic/Linarith",
                "Mathlib/Unused",
            ]:
                write(mathlib / ".lake" / "build" / "lib" / "lean" / f"{module}.olean")
                write(mathlib / ".lake" / "build" / "ir" / f"{module}.c")

            closure = prune_lake_cache.collect_mathlib_closure(project_root, packages_root)
            self.assertEqual(
                closure,
                {"Mathlib.Data.Nat.Basic", "Mathlib.Init.Zero", "Mathlib.Tactic.Linarith"},
            )

            prune_lake_cache.prune_package(mathlib, closure)
            prune_lake_cache.prune_root_mathlib_cache(project_root)

            self.assertTrue((mathlib / "Mathlib" / "Data" / "Nat" / "Basic.lean").is_file())
            self.assertTrue((mathlib / "Mathlib" / "Init" / "Zero.lean").is_file())
            self.assertTrue((mathlib / "Mathlib" / "Tactic" / "Linarith.lean").is_file())
            self.assertFalse((mathlib / "Mathlib" / "Unused.lean").exists())
            self.assertFalse((mathlib / ".lake" / "build" / "lib" / "lean" / "Mathlib" / "Unused.olean").exists())
            self.assertFalse((mathlib / ".lake" / "build" / "ir" / "Mathlib" / "Unused.c").exists())
            self.assertTrue((mathlib / ".lake" / "build" / "lib" / "lean" / "Mathlib" / "Data" / "Nat" / "Basic.olean").is_file())
            self.assertFalse((mathlib / "README.md").exists())
            self.assertFalse((mathlib / ".github").exists())
            self.assertFalse((mathlib / "Mathlib" / "Unused.ltar").exists())
            self.assertFalse((project_root / ".lake" / "build" / "lib" / "lean" / "Mathlib").exists())
            self.assertFalse((project_root / ".lake" / "build" / "lib" / "lean" / "Mathlib.olean").exists())

    def test_keeps_all_non_mathlib_modules(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            project_root = Path(tmp) / "project"
            packages_root = project_root / ".lake" / "packages"
            package = packages_root / "aesop"

            write(package / "Aesop" / "Core.lean")
            write(package / "Aesop" / "Unused.lean")
            write(package / ".lake" / "build" / "lib" / "lean" / "Aesop" / "Core.olean")
            write(package / ".lake" / "build" / "lib" / "lean" / "Aesop" / "Unused.olean")
            write(package / "docs" / "guide.md", "unused metadata\n")

            prune_lake_cache.prune_package(package, mathlib_closure=set())

            self.assertTrue((package / "Aesop" / "Core.lean").is_file())
            self.assertTrue((package / "Aesop" / "Unused.lean").is_file())
            self.assertTrue((package / ".lake" / "build" / "lib" / "lean" / "Aesop" / "Core.olean").is_file())
            self.assertTrue((package / ".lake" / "build" / "lib" / "lean" / "Aesop" / "Unused.olean").is_file())
            self.assertFalse((package / "docs").exists())


if __name__ == "__main__":
    unittest.main()
