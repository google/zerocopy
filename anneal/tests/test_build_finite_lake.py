# Copyright 2026 The Fuchsia Authors
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
"""Publisher recipe fixtures; fake compiler calls, no native tool execution."""
import importlib.util
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / "build-finite-lake.py"
SPEC = importlib.util.spec_from_file_location("build_finite_lake", SCRIPT)
producer = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(producer)


class FiniteRecipeTests(unittest.TestCase):
    def fixture(self):
        temp = tempfile.TemporaryDirectory(dir=os.environ.get("ANNEAL_SDK_TEST_ROOT"))
        self.addCleanup(temp.cleanup)
        root = Path(temp.name).resolve()
        (root / "lean/bin").mkdir(parents=True)
        source = root / "input.lean"
        source.write_text("-- trusted source\n")
        return root, source

    def test_exact_pinned_compile_link_paths_and_relative_native_loader_recipe(self):
        for platform, origin in [("aarch64-darwin", "@executable_path"), ("x86_64-darwin", "@executable_path"),
                                 ("aarch64-linux", "$ORIGIN"), ("x86_64-linux", "$ORIGIN")]:
            with self.subTest(platform=platform):
                root, source = self.fixture()
                calls = []
                def compiler(argv, **kwargs):
                    calls.append((argv, kwargs))
                    if argv[0].endswith("/bin/lean"):
                        Path(argv[argv.index("-c") + 1]).write_text("/* emitted */")
                    else:
                        Path(argv[argv.index("-o") + 1]).write_bytes(b"fresh executable fixture")
                with patch.dict(os.environ, {"LEAN_PATH":"untrusted-imports", "LEAN_SYSROOT":"untrusted-runtime"}), patch.object(producer.subprocess, "run", side_effect=compiler):
                    producer.build(root, source, platform)
                self.assertEqual(len(calls), 2)
                self.assertEqual(calls[0][0][0], str(root / "lean/bin/lean"))
                argv, options = calls[1]
                runtime_links = (["-lInit_shared", "-lleanshared_2", "-lleanshared_1", "-lleanshared"]
                                 if platform.endswith("-linux") else [])
                # ELF executable references must resolve from direct providers
                # after the generated object and Lake; Darwin keeps its exact
                # previously validated command, including relative loader paths.
                generated_c = calls[0][0][calls[0][0].index("-c") + 1]
                self.assertEqual(argv, [str(root / "lean/bin/leanc"), "-O1", "-rdynamic", "-leanshared",
                                       generated_c, "-L", str(root / "lean/lib/lean"), "-lLake_shared",
                                       *runtime_links,
                                       "-Wl,-rpath," + origin + "/../lib/lean", "-Wl,-rpath," + origin + "/../lib",
                                       "-o", str(root / "lean/bin/anneal-finite-lake")])
                for _, kwargs in calls:
                    self.assertTrue(kwargs["check"])
                    self.assertEqual(kwargs["env"]["LEAN_PATH"], str(root / "lean/lib/lean"))
                    self.assertEqual(kwargs["env"]["LEAN_SYSROOT"], str(root / "lean"))
                self.assertEqual((root / "lean/src/anneal/FiniteLake.lean").read_bytes(), source.read_bytes())
                self.assertEqual((root / "lean/src/anneal/build-finite-lake.py").read_bytes(), SCRIPT.read_bytes())

    def test_never_compiles_into_an_assembled_or_existing_publisher(self):
        root, source = self.fixture()
        (root / "lean-sdk").mkdir()
        with patch.object(producer.subprocess, "run") as compiler:
            with self.assertRaisesRegex(ValueError, "precede SDK"):
                producer.build(root, source, "aarch64-darwin")
            compiler.assert_not_called()
        root, source = self.fixture()
        (root / "lean/src/anneal").mkdir(parents=True)
        with patch.object(producer.subprocess, "run") as compiler:
            with self.assertRaises(FileExistsError):
                producer.build(root, source, "aarch64-darwin")
            compiler.assert_not_called()

    def test_compiler_failure_is_retained_not_retried_as_stock(self):
        root, source = self.fixture()
        with patch.object(producer.subprocess, "run", side_effect=RuntimeError("compile failed")) as compiler:
            with self.assertRaisesRegex(RuntimeError, "compile failed"):
                producer.build(root, source, "aarch64-darwin")
            self.assertEqual(compiler.call_count, 1)
        self.assertTrue((root / "lean/src/anneal/FiniteLake.lean").exists())
        self.assertFalse((root / "lean/bin/anneal-finite-lake").exists())

    def test_dangling_publisher_outputs_are_rejected_before_compile(self):
        for relative in ["lean-sdk", "lean/bin/anneal-finite-lake", "lean/src/anneal"]:
            root, source = self.fixture()
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.symlink_to(root / "missing")
            with patch.object(producer.subprocess, "run") as compiler:
                with self.assertRaises((ValueError, FileExistsError)):
                    producer.build(root, source, "aarch64-darwin")
                compiler.assert_not_called()

    def test_live_and_dangling_staging_ancestors_rejected_before_writes(self):
        for relative in ["lean/src", "lean/bin", "lean/bin/lean", "lean/bin/leanc"]:
            for live in [False, True]:
                with self.subTest(relative=relative, live=live):
                    root, source = self.fixture()
                    path = root / relative
                    target = root / "redirected-fixture"
                    if path.is_dir():
                        path.rename(target)
                    if live:
                        if relative in ["lean/src", "lean/bin"]:
                            target.mkdir(exist_ok=True)
                            (target / "sentinel").write_bytes(b"unchanged")
                        else:
                            target.write_bytes(b"unchanged")
                    elif target.exists():
                        target.rename(root / "retained-fixture")
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.symlink_to(target)
                    with patch.object(producer.subprocess, "run") as compiler:
                        with self.assertRaisesRegex(ValueError, "physical"):
                            producer.build(root, source, "aarch64-darwin")
                        compiler.assert_not_called()
                    self.assertEqual(source.read_text(), "-- trusted source\n")
                    if live:
                        if target.is_dir():
                            self.assertEqual(sorted(p.name for p in target.iterdir()), ["sentinel"])
                            self.assertEqual((target / "sentinel").read_bytes(), b"unchanged")
                        else:
                            self.assertEqual(target.read_bytes(), b"unchanged")
                    else:
                        self.assertFalse(target.exists())
                    if relative != "lean/src":
                        self.assertFalse((root / "lean/src/anneal").exists())
