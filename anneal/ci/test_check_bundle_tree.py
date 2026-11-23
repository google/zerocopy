# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for confined bundle validation (`check_bundle_tree.py`)."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import check_bundle_tree


SCRIPT = Path(__file__).resolve().parent / "check_bundle_tree.py"


def populate_valid_bundle(root: Path) -> None:
    for rel_dir in (
        "rust/bin",
        "rust/lib",
        "lean/bin",
        "lean/lib",
        "bin",
        "share/anneal/prebuilt",
        "share/anneal/trusted/audit",
    ):
        (root / rel_dir).mkdir(parents=True, exist_ok=True)
    for rel_file in check_bundle_tree.FULL_BUNDLE_FILES:
        (root / rel_file).write_text("placeholder\n")
    # Legitimate internal chained `.so` symlinks inside `lean/lib`.
    (root / "lean/lib/libc++abi.so.1.0").write_text("elf\n")
    (root / "lean/lib/libc++abi.so.1").symlink_to("libc++abi.so.1.0")
    (root / "lean/lib/libc++abi.so").symlink_to("libc++abi.so.1")


class CheckBundleTreeTests(unittest.TestCase):
    def run_cli(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), *args],
            capture_output=True,
            text=True,
        )

    def test_valid_full_discover_and_lean_only_modes_pass(self):
        with tempfile.TemporaryDirectory() as tmp:
            cache = Path(tmp) / "cache"
            root = cache / "anneal/toolchain/extracted"
            populate_valid_bundle(root)
            # `exocrate` leaves a sibling `.lock` file next to the bundle dir.
            (cache / "anneal/toolchain/extracted.lock").write_text("")

            res = self.run_cli("--cache-root", str(cache), "--root", str(root))
            self.assertEqual(res.returncode, 0, res.stderr)
            env_map = dict(
                line.split("=", 1) for line in res.stdout.strip().splitlines()
            )
            self.assertEqual(env_map["XDG_CACHE_HOME"], str(cache.resolve()))
            self.assertEqual(
                env_map["RUSTC"], str(root.resolve() / "rust/bin/rustc")
            )
            self.assertEqual(
                env_map["ANNEAL_LEAN"], str(root.resolve() / "lean/bin/lean")
            )

            diag = Path(tmp) / "installation.json"
            disc = self.run_cli(
                "--cache-root",
                str(cache),
                "--discover-single",
                "--diagnostics",
                str(diag),
                "--source-revision",
                "deadbeef",
            )
            self.assertEqual(disc.returncode, 0, disc.stderr)
            recorded = json.loads(diag.read_text())
            self.assertEqual(recorded["source_revision"], "deadbeef")
            self.assertEqual(
                recorded["fresh_installation_root"], str(root.resolve())
            )

            lean_root = Path(tmp) / "lean-only"
            (lean_root / "lean/bin").mkdir(parents=True)
            (lean_root / "lean/bin/lean").write_text("lean\n")
            lean_res = self.run_cli("--root", str(lean_root), "--lean-only")
            self.assertEqual(lean_res.returncode, 0, lean_res.stderr)
            self.assertEqual(
                lean_res.stdout.strip(),
                f"ANNEAL_TEST_INSTALL_ROOT={lean_root.resolve()}",
            )

    def test_rejects_symlinked_ancestors_to_external_or_internal_dirs(self):
        for ancestor, target_subpath in (
            ("rust/bin", "rustc"),
            ("lean/bin", "lean"),
            ("bin", "anneal-rustc-capture"),
            ("rust/lib", "libstd.so"),
            ("share/anneal", "correspondence-provenance.json"),
        ):
            with (
                self.subTest(ancestor=ancestor),
                tempfile.TemporaryDirectory() as tmp,
            ):
                tmp_path = Path(tmp)
                external = tmp_path / "checkout_poison"
                external.mkdir()
                (external / target_subpath).write_text("poison\n")
                if ancestor == "rust/bin":
                    (external / "rustdoc").write_text("poison\n")
                if ancestor == "share/anneal":
                    (external / "trusted/audit").mkdir(parents=True)
                    (
                        external / "trusted/audit/TrustedBoundary.lean"
                    ).write_text("x\n")

                cache = tmp_path / "cache"
                root = cache / "anneal/toolchain/extracted"
                populate_valid_bundle(root)
                victim = root / ancestor
                shutil.rmtree(victim)
                victim.symlink_to(external)

                res = self.run_cli(
                    "--cache-root", str(cache), "--root", str(root)
                )
                self.assertNotEqual(res.returncode, 0, ancestor)

        # Even a relative directory symlink staying inside `root` is rejected.
        with tempfile.TemporaryDirectory() as tmp:
            cache = Path(tmp) / "cache"
            root = cache / "anneal/toolchain/extracted"
            populate_valid_bundle(root)
            alt = root / "alt_bin"
            shutil.move(str(root / "bin"), str(alt))
            (root / "bin").symlink_to("alt_bin")
            res = self.run_cli("--cache-root", str(cache), "--root", str(root))
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("directory symlink", res.stderr)

        # `lean-only` also rejects a symlinked `lean/bin` ancestor.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            ext_bin = tmp_path / "ext_bin"
            ext_bin.mkdir()
            (ext_bin / "lean").write_text("poison\n")
            lean_root = tmp_path / "lean_root"
            (lean_root / "lean").mkdir(parents=True)
            (lean_root / "lean/bin").symlink_to(ext_bin)
            res = self.run_cli("--root", str(lean_root), "--lean-only")
            self.assertNotEqual(res.returncode, 0)

    def test_rejects_external_dangling_boomerang_cache_symlinks_and_fifos(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            outside_file = tmp_path / "outside.so"
            outside_file.write_text("evil\n")

            # 1. Relative file symlink escaping bundle root.
            cache = tmp_path / "c1"
            root = cache / "anneal/toolchain/extracted"
            populate_valid_bundle(root)
            (root / "lean/lib/escape.so").symlink_to(
                "../../../../../../outside.so"
            )
            self.assertNotEqual(
                self.run_cli(
                    "--cache-root", str(cache), "--root", str(root)
                ).returncode,
                0,
            )

            # 2. Absolute file symlink (even pointing inside root).
            cache2 = tmp_path / "c2"
            root2 = cache2 / "anneal/toolchain/extracted"
            populate_valid_bundle(root2)
            (root2 / "lean/lib/abs.so").symlink_to(
                root2.resolve() / "lean/lib/libc++abi.so.1.0"
            )
            self.assertNotEqual(
                self.run_cli(
                    "--cache-root", str(cache2), "--root", str(root2)
                ).returncode,
                0,
            )

            # 3. Boomerang relative symlink leaving root then re-entering.
            cache3 = tmp_path / "c3"
            root3 = cache3 / "anneal/toolchain/extracted"
            populate_valid_bundle(root3)
            (root3 / "lean/lib/boomerang.so").symlink_to(
                "../../../extracted/lean/lib/libc++abi.so.1.0"
            )
            self.assertNotEqual(
                self.run_cli(
                    "--cache-root", str(cache3), "--root", str(root3)
                ).returncode,
                0,
            )

            # 4. Dangling symlink inside bundle.
            cache4 = tmp_path / "c4"
            root4 = cache4 / "anneal/toolchain/extracted"
            populate_valid_bundle(root4)
            (root4 / "lean/lib/dangling.so").symlink_to("missing.so")
            self.assertNotEqual(
                self.run_cli(
                    "--cache-root", str(cache4), "--root", str(root4)
                ).returncode,
                0,
            )

            # 5. Symlinked cache ancestor (`anneal/toolchain -> real_dir`).
            cache5 = tmp_path / "c5"
            real_tc = tmp_path / "real_tc"
            populate_valid_bundle(real_tc / "extracted")
            (cache5 / "anneal").mkdir(parents=True)
            (cache5 / "anneal/toolchain").symlink_to(real_tc)
            self.assertNotEqual(
                self.run_cli(
                    "--cache-root",
                    str(cache5),
                    "--root",
                    str(cache5 / "anneal/toolchain/extracted"),
                ).returncode,
                0,
            )

            # 6. Special file (FIFO) inside bundle.
            cache6 = tmp_path / "c6"
            root6 = cache6 / "anneal/toolchain/extracted"
            populate_valid_bundle(root6)
            os.mkfifo(root6 / "lean/lib/pipe.fifo")
            self.assertNotEqual(
                self.run_cli(
                    "--cache-root", str(cache6), "--root", str(root6)
                ).returncode,
                0,
            )

            # 7. Unreadable (`0o111` / `0o000`) directory hiding an escaping
            # symlink must fail closed via `os.walk(..., onerror=...)`.
            if os.geteuid() != 0:
                for hidden_mode in (0o111, 0o000):
                    cache7 = tmp_path / f"c7_{hidden_mode:o}"
                    root7 = cache7 / "anneal/toolchain/extracted"
                    populate_valid_bundle(root7)
                    hidden = root7 / "lean/lib/hidden"
                    hidden.mkdir()
                    (hidden / "escape.so").symlink_to(outside_file)
                    hidden.chmod(hidden_mode)
                    try:
                        res7 = self.run_cli(
                            "--cache-root", str(cache7), "--root", str(root7)
                        )
                        self.assertNotEqual(
                            res7.returncode, 0, oct(hidden_mode)
                        )
                        self.assertIn("cannot traverse", res7.stderr)
                    finally:
                        hidden.chmod(0o755)


if __name__ == "__main__":
    unittest.main()
