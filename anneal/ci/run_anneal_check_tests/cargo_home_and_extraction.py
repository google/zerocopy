# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Tests of the mounted `CARGO_HOME` guard and prepared-crate extraction in
`run_anneal_check.sh`."""

import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import tempfile

from run_anneal_check_tests.support import SCRIPT, shell_function


class CargoHomeGuardCases:
    NAMES = ("config", "config.toml", "credentials", "credentials.toml", "bin")
    GUARD_CALL = 'guard_mounted_cargo_home "${CARGO_HOME:-}" /cargo-home'

    def run_guard(self, cargo_home: str, mount: Path) -> subprocess.CompletedProcess[str]:
        text = SCRIPT.read_text(encoding="utf-8")
        functions = shell_function(text, "require_inert_cargo_home") + shell_function(
            text, "guard_mounted_cargo_home"
        )
        return subprocess.run(
            ["bash", "-euo", "pipefail", "-c",
             functions + 'guard_mounted_cargo_home "$1" "$2"',
             "guard", cargo_home, str(mount)],
            capture_output=True,
            text=True,
            check=False,
        )

    @staticmethod
    def seed(path: Path, kind: str) -> None:
        if kind == "file":
            path.write_text("")
        elif kind == "dir":
            path.mkdir()
        else:
            path.symlink_to(path.parent / "missing")

    @staticmethod
    def spellings(root: Path, mount: Path) -> list[str]:
        link = root / "link"
        if not link.exists():
            link.symlink_to(mount, target_is_directory=True)
        return [str(mount), f"{mount}/", f"{mount}//", f"{mount}/.",
                f"{mount}/../{mount.name}", str(link)]

    def test_clean_mount_is_accepted(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            mount = Path(tmp) / "cargo-home"
            (mount / "registry").mkdir(parents=True)
            (mount / ".package-cache").write_text("")
            for cargo_home in self.spellings(Path(tmp), mount):
                with self.subTest(cargo_home=cargo_home):
                    self.assertEqual(self.run_guard(cargo_home, mount).returncode, 0)

    def test_preset_or_adopted_mount_with_steering_entry_is_rejected(self) -> None:
        for name in self.NAMES:
            for kind in ("file", "dir", "dangling-symlink"):
                with tempfile.TemporaryDirectory() as tmp:
                    mount = Path(tmp) / "cargo-home"
                    mount.mkdir()
                    self.seed(mount / name, kind)
                    for cargo_home in self.spellings(Path(tmp), mount):
                        with self.subTest(name=name, kind=kind, cargo_home=cargo_home):
                            result = self.run_guard(cargo_home, mount)
                            self.assertEqual(result.returncode, 1)
                            self.assertIn(f"it contains {name}", result.stderr)

    def test_other_cargo_home_does_not_inspect_mount(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            mount = Path(tmp) / "cargo-home"
            mount.mkdir()
            (mount / "config.toml").write_text("")
            other = Path(tmp) / "other"
            other.mkdir()
            for cargo_home in ("", str(other), f"{mount}-2"):
                with self.subTest(cargo_home=cargo_home):
                    self.assertEqual(self.run_guard(cargo_home, mount).returncode, 0)

    def test_guard_runs_once_cargo_home_is_final(self) -> None:
        lines = SCRIPT.read_text(encoding="utf-8").splitlines()
        calls = [i for i, line in enumerate(lines) if line == self.GUARD_CALL]
        self.assertEqual(len(calls), 1)
        exports = [i for i, line in enumerate(lines)
                   if re.match(r"\s*export CARGO_HOME=", line)]
        first_use = lines.index('case "$MODE" in')
        self.assertTrue(exports)
        self.assertLess(max(exports), calls[0])
        self.assertLess(calls[0], first_use)


class PreparedCrateExtractionCases:
    def program(self) -> str:
        text = SCRIPT.read_text(encoding="utf-8")
        match = re.search(
            r"PREPARED_MANIFEST=\"\$\(/usr/bin/python3 -I -B - <<'PY'\n"
            r"(.*?)^PY$",
            text,
            re.M | re.S,
        )
        if match is None:
            raise AssertionError("prepared-crate extraction program not found")
        return match.group(1)

    def run_extract(self, root: Path, seed) -> tuple[subprocess.CompletedProcess[str], Path]:
        diag = root / "diag"
        target = root / "target"
        prepared = target / "package"
        diag.mkdir()
        prepared.mkdir(parents=True)
        (diag / "package-metadata.json").write_text(json.dumps(
            {"packages": [{"name": "cargo-anneal", "version": "9.9.9"}]}
        ))
        src = root / "src" / "cargo-anneal-9.9.9"
        src.mkdir(parents=True)
        (src / "Cargo.toml").write_text("[package]\n")
        with tarfile.open(prepared / "cargo-anneal-9.9.9.crate", "w:gz") as tf:
            tf.add(src, arcname="cargo-anneal-9.9.9")
        seed(prepared / "cargo-anneal-9.9.9")
        env = dict(os.environ, ANNEAL_TEST_DIAGNOSTICS=str(diag),
                   CARGO_TARGET_DIR=str(target))
        result = subprocess.run(
            [sys.executable, "-I", "-B", "-"],
            input=self.program(),
            capture_output=True,
            text=True,
            env=env,
            check=False,
        )
        return result, prepared / "cargo-anneal-9.9.9"

    def test_stale_extraction_is_removed(self) -> None:
        def seed(extracted: Path) -> None:
            extracted.mkdir()
            (extracted / "stale.rs").write_text("")

        with tempfile.TemporaryDirectory() as tmp:
            result, extracted = self.run_extract(Path(tmp), seed)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.strip(), str(extracted / "Cargo.toml"))
            self.assertFalse((extracted / "stale.rs").exists())
            self.assertTrue((extracted / "Cargo.toml").is_file())

    def test_symlinked_extraction_is_replaced(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            outside = Path(tmp) / "outside"
            outside.mkdir()
            (outside / "stale.rs").write_text("")

            def seed(extracted: Path) -> None:
                extracted.symlink_to(outside, target_is_directory=True)

            result, extracted = self.run_extract(Path(tmp), seed)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertFalse(extracted.is_symlink())
            self.assertTrue((extracted / "Cargo.toml").is_file())
            self.assertTrue((outside / "stale.rs").is_file())
