# Copyright 2026 The Fuchsia Authors
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
"""Support publisher recipe controls with a fake compiler only."""
import importlib.util
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / "build-anneal-support.py"
CANONICAL_SOURCE = SCRIPT.parent / "v1/src/Anneal.lean"
SPEC = importlib.util.spec_from_file_location("build_anneal_support", SCRIPT)
producer = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(producer)


class SupportRecipeTests(unittest.TestCase):
    def fixture(self, platform="aarch64-darwin"):
        temp = tempfile.TemporaryDirectory(dir=os.environ.get("ANNEAL_SDK_TEST_ROOT"))
        self.addCleanup(temp.cleanup)
        root = Path(temp.name).resolve()
        for relative in ["lean/bin", "aeneas/backends/lean/.lake/build/lib/lean",
                         "aeneas/packages/batteries/.lake/build/lib/lean", "aeneas/packages/Cli"]:
            (root / relative).mkdir(parents=True)
        plugin = root / "aeneas/backends/lean/.lake/build/lib" / ("libaeneas_AeneasMeta." + ("dylib" if platform.endswith("-darwin") else "so"))
        plugin.write_bytes(b"selected plugin fixture")
        source = root / "input.lean"
        source.write_text("import Aeneas.Std.Core\n-- original consumer reflection\n")
        return root, source, plugin

    def test_single_exact_family_compile_no_imported_package_build_or_native_link(self):
        for platform in ["aarch64-darwin", "x86_64-linux"]:
            with self.subTest(platform=platform):
                root, _, plugin = self.fixture(platform)
                # Publish the exact canonical body under the retained module
                # name; the input checkout filename never reaches the compiler.
                source = CANONICAL_SOURCE
                calls = []
                def compiler(argv, **kwargs):
                    calls.append((argv, kwargs))
                    for flag in ["-o", "-i"]:
                        Path(argv[argv.index(flag) + 1]).write_bytes(b"fresh family fixture")
                with patch.dict(os.environ, {"LEAN_PATH":"ambient-imports", "LEAN_SYSROOT":"ambient-runtime"}), patch.object(producer.subprocess, "run", side_effect=compiler):
                    producer.build(root, source, platform)
                self.assertEqual(len(calls), 1)
                argv, options = calls[0]
                self.assertEqual(argv[0], str(root / "lean/bin/lean"))
                self.assertEqual(argv[-1], str(root / "lean/src/lean/AnnealSupport.lean"))
                self.assertIn("--root=" + str(root / "lean/src/lean"), argv)
                self.assertIn("--load-dynlib=" + str(plugin), argv)
                self.assertNotIn("-c", argv)
                self.assertEqual(options["env"]["LEAN_PATH"], os.pathsep.join(map(str, [
                    root / "lean/lib/lean", root / "aeneas/backends/lean/.lake/build/lib/lean",
                    root / "aeneas/packages/batteries/.lake/build/lib/lean"])))
                self.assertEqual(options["env"]["LEAN_SYSROOT"], str(root / "lean"))
                self.assertEqual((root / "lean/src/lean/AnnealSupport.lean").read_bytes(), source.read_bytes())
                self.assertEqual((root / "lean/src/anneal/build-anneal-support.py").read_bytes(), SCRIPT.read_bytes())

    def test_existing_sdk_or_support_never_repaired(self):
        for relative in ["lean-sdk", "lean/lib/lean/AnnealSupport.olean", "lean/src/lean/AnnealSupport.lean"]:
            with self.subTest(relative=relative):
                root, source, _ = self.fixture()
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.mkdir() if relative == "lean-sdk" else path.write_bytes(b"existing")
                with patch.object(producer.subprocess, "run") as compiler:
                    with self.assertRaises((ValueError, FileExistsError)):
                        producer.build(root, source, "aarch64-darwin")
                    compiler.assert_not_called()

    def test_missing_family_or_compile_error_retains_failure_without_retry(self):
        root, source, _ = self.fixture()
        with patch.object(producer.subprocess, "run") as compiler:
            with self.assertRaisesRegex(ValueError, "complete olean/ilean"):
                producer.build(root, source, "aarch64-darwin")
            self.assertEqual(compiler.call_count, 1)
        self.assertTrue((root / "lean/src/lean/AnnealSupport.lean").exists())
        root, source, _ = self.fixture()
        with patch.object(producer.subprocess, "run", side_effect=RuntimeError("compile failed")) as compiler:
            with self.assertRaisesRegex(RuntimeError, "compile failed"):
                producer.build(root, source, "aarch64-darwin")
            self.assertEqual(compiler.call_count, 1)

    def test_dangling_output_and_runtime_staging_links_rejected_before_compile(self):
        for relative in ["lean-sdk", "lean/lib/lean/AnnealSupport.olean",
                         "lean/src/lean/AnnealSupport.lean", "lean/src", "lean/lib", "lean"]:
            with self.subTest(relative=relative):
                root, source, _ = self.fixture()
                path = root / relative
                if path.is_dir():
                    # Keep the prior fixture bytes while installing a deliberate
                    # dangling link at the runtime staging path.
                    path.rename(root / "retained-fixture-runtime")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.symlink_to(root / "missing-output")
                with patch.object(producer.subprocess, "run") as compiler:
                    with self.assertRaises((ValueError, FileExistsError)):
                        producer.build(root, source, "aarch64-darwin")
                    compiler.assert_not_called()
