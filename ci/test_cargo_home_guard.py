# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for the mounted `CARGO_HOME` guard in ci/scripts/*.sh."""

from pathlib import Path
import re
import subprocess
import tempfile
import unittest


REPO_ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = REPO_ROOT / "ci" / "scripts"
NAMES = ("config", "config.toml", "credentials", "credentials.toml", "bin")
GUARD_CALL = 'guard_mounted_cargo_home "${CARGO_HOME:-}" /cargo-home'


def shell_function(text: str, name: str) -> str:
    match = re.search(rf"^{name}\(\) \{{\n.*?^\}}\n", text, re.M | re.S)
    if match is None:
        raise AssertionError(f"function {name} not found")
    return match.group(0)


def run_guard(script: Path, cargo_home: str, mount: Path) -> subprocess.CompletedProcess[str]:
    text = script.read_text(encoding="utf-8")
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


def seed(path: Path, kind: str) -> None:
    if kind == "file":
        path.write_text("")
    elif kind == "dir":
        path.mkdir()
    else:
        path.symlink_to(path.parent / "missing")


def spellings(root: Path, mount: Path) -> list[str]:
    link = root / "link"
    if not link.exists():
        link.symlink_to(mount, target_is_directory=True)
    return [str(mount), f"{mount}/", f"{mount}//", f"{mount}/.",
            f"{mount}/../{mount.name}", str(link)]


class CargoHomeGuardTests(unittest.TestCase):
    def cargo_home_scripts(self) -> list[Path]:
        """Scripts that may run cargo with the mounted `/cargo-home` cache."""
        scripts = [
            path for path in sorted(SCRIPTS.glob("*.sh"))
            if "/cargo-home" in path.read_text(encoding="utf-8")
        ]
        self.assertIn(SCRIPTS / "run_exocrate_test.sh", scripts)
        return scripts

    def test_guard_runs_once_cargo_home_is_final(self) -> None:
        for script in self.cargo_home_scripts():
            with self.subTest(script=script.name):
                lines = script.read_text(encoding="utf-8").splitlines()
                calls = [i for i, line in enumerate(lines) if line == GUARD_CALL]
                self.assertEqual(len(calls), 1)
                exports = [i for i, line in enumerate(lines)
                           if re.match(r"\s*export CARGO_HOME=", line)]
                cargo_runs = [i for i, line in enumerate(lines)
                              if re.match(r"cargo ", line)]
                self.assertTrue(exports)
                self.assertTrue(cargo_runs)
                self.assertLess(max(exports), calls[0])
                self.assertLess(calls[0], min(cargo_runs))

    def test_clean_mount_is_accepted(self) -> None:
        for script in self.cargo_home_scripts():
            with tempfile.TemporaryDirectory() as tmp:
                mount = Path(tmp) / "cargo-home"
                (mount / "registry").mkdir(parents=True)
                for cargo_home in spellings(Path(tmp), mount):
                    with self.subTest(script=script.name, cargo_home=cargo_home):
                        result = run_guard(script, cargo_home, mount)
                        self.assertEqual(result.returncode, 0, result.stderr)

    def test_preset_or_adopted_mount_with_steering_entry_is_rejected(self) -> None:
        for script in self.cargo_home_scripts():
            for name in NAMES:
                for kind in ("file", "dir", "dangling-symlink"):
                    with tempfile.TemporaryDirectory() as tmp:
                        mount = Path(tmp) / "cargo-home"
                        mount.mkdir()
                        seed(mount / name, kind)
                        for cargo_home in spellings(Path(tmp), mount):
                            with self.subTest(script=script.name, name=name,
                                              kind=kind, cargo_home=cargo_home):
                                result = run_guard(script, cargo_home, mount)
                                self.assertEqual(result.returncode, 1)
                                self.assertIn(f"it contains {name}", result.stderr)

    def test_other_cargo_home_does_not_inspect_mount(self) -> None:
        for script in self.cargo_home_scripts():
            with tempfile.TemporaryDirectory() as tmp:
                mount = Path(tmp) / "cargo-home"
                mount.mkdir()
                (mount / "config.toml").write_text("")
                other = Path(tmp) / "other"
                other.mkdir()
                for cargo_home in ("", str(other), f"{mount}-2"):
                    with self.subTest(script=script.name, cargo_home=cargo_home):
                        self.assertEqual(
                            run_guard(script, cargo_home, mount).returncode, 0
                        )


if __name__ == "__main__":
    unittest.main()
