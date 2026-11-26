# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `anneal/ci/run_anneal_check.sh`.

`run_anneal_check.sh` builds its own omnibus archive for `ws-test` and
`installed-smoke` instead of `nix build .#omnibus-archive`. These tests pin
that archive's filtering and verification contract to `flake.nix` so a change
to one side fails CI rather than silently drifting from the shipped archive.
"""

import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import tempfile
import unittest


ANNEAL_ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ANNEAL_ROOT / "ci" / "run_anneal_check.sh"
FLAKE = ANNEAL_ROOT / "flake.nix"


def omnibus_flake_section() -> str:
    text = FLAKE.read_text(encoding="utf-8")
    start = text.index("omnibus-archive = pkgs.stdenv.mkDerivation {")
    end = text.index("release-check-python =", start)
    section = text[start:end]
    # Undo Nix's `''${` escape and map the Nix attribute to the shell name the
    # script uses for the same rustc target triple.
    return section.replace("''${", "${").replace("$rustTarget", "$rust_target")


def shell_function(text: str, name: str) -> str:
    match = re.search(rf"^{name}\(\) \{{\n.*?^\}}\n", text, re.M | re.S)
    if match is None:
        raise AssertionError(f"function {name} not found")
    return match.group(0)


def pack_function() -> str:
    return shell_function(SCRIPT.read_text(encoding="utf-8"), "pack_omnibus_archive")


def array_items(text: str, name: str) -> list[str]:
    """Collect items of every `name=(...)`/`name+=(...)` block, in order."""
    items = []
    pattern = rf"^\s*(?:local )?{name}\+?=\(\n(.*?)^\s*\)\s*$"
    for block in re.findall(pattern, text, re.M | re.S):
        for line in block.splitlines():
            item = line.strip()
            if not item:
                continue
            if len(item) >= 2 and item[0] == item[-1] and item[0] in "'\"":
                item = item[1:-1]
            items.append(item)
    return items


def excludes(text: str) -> list[str]:
    return sorted(re.findall(r'--exclude="([^"]+)"', text))


def fixed_tar_flags(text: str) -> list[str]:
    return [
        item
        for item in array_items(text, "tar_args")
        if item.startswith("--")
        and not item.startswith(("--exclude=", "--transform="))
    ]


def lock_check_members(text: str) -> list[str]:
    match = re.search(
        r'tar -C "\$[A-Za-z_{}/]+lock_check" -xf - \\\n(.*?)\n\s*LOCK_CHECK_DIR=',
        text,
        re.S,
    )
    if match is None:
        raise AssertionError("library-lock extraction not found")
    return [m.strip(" \\") for m in match.group(1).splitlines()]


def lock_check_program(text: str) -> str:
    match = re.search(r"<< 'PYEOF'\n(.*?)^PYEOF$", text, re.M | re.S)
    if match is None:
        raise AssertionError("library-lock verifier not found")
    return match.group(1)


class OmnibusArchiveParityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.flake = omnibus_flake_section()
        self.script = pack_function()

    def test_excludes_match_flake(self) -> None:
        flake_excludes = excludes(self.flake)
        self.assertGreaterEqual(len(flake_excludes), 50)
        self.assertEqual(excludes(self.script), flake_excludes)

    def test_deterministic_tar_flags_match_flake(self) -> None:
        flake_flags = fixed_tar_flags(self.flake)
        for flag in ("--sort=name", "--mtime=@0", "--owner=0", "--group=0",
                     "--numeric-owner", "--hard-dereference", "--anchored"):
            self.assertIn(flag, flake_flags)
        self.assertEqual(fixed_tar_flags(self.script), flake_flags)

    def test_transforms_match_flake(self) -> None:
        pattern = r'--transform="([^"]+)"'
        self.assertEqual(
            re.findall(pattern, self.script), re.findall(pattern, self.flake)
        )
        self.assertEqual(len(re.findall(pattern, self.flake)), 2)

    def test_leak_bans_match_flake(self) -> None:
        flake_bans = array_items(self.flake, "excluded_patterns")
        self.assertGreaterEqual(len(flake_bans), 12)
        self.assertEqual(array_items(self.script, "excluded_patterns"), flake_bans)

    def test_required_entries_match_flake(self) -> None:
        flake_entries = array_items(self.flake, "expected_entries")
        for entry in ("lean/lib/lean/Init.olean", "lean/lib/lean/Init.ir",
                      "rust/bin/rustdoc",
                      "rust/lib/rustlib/$rust_target/bin/rust-lld",
                      "rust/lib/rustlib/$rust_target/bin/gcc-ld/ld.lld",
                      "lean/lib/lean/libleanshared.so"):
            self.assertIn(entry, flake_entries)
        self.assertEqual(array_items(self.script, "expected_entries"), flake_entries)

    def test_duplicate_library_handling_matches_flake(self) -> None:
        for snippet in (
            "for prefix in libLLVM librustc_driver-; do",
            'ln -s "../../../$lib_name"',
            "cmp -s \"$lib_path\" \"$dup_path\"",
            '"^-.* rust/lib/rustlib/$rust_target/lib/(libLLVM|librustc_driver-)"',
            'grep -Eq "^rust/lib/rustlib/$rust_target/lib/$prefix"',
        ):
            self.assertIn(snippet, self.flake)
            self.assertIn(snippet, self.script)
        prefix_loop = "for prefix in libLLVM librustc_driver-; do"
        self.assertEqual(
            self.script.count(prefix_loop), self.flake.count(prefix_loop)
        )

    def test_library_lock_verification_matches_flake(self) -> None:
        self.assertEqual(
            lock_check_members(self.script), lock_check_members(self.flake)
        )
        self.assertEqual(
            lock_check_program(self.script), lock_check_program(self.flake)
        )

    def test_compression_matches_flake(self) -> None:
        self.assertIn("-12 --long=27", self.flake)
        self.assertIn("-12 --long=27", self.script)

    def test_only_pack_function_tars_toolchains(self) -> None:
        text = SCRIPT.read_text(encoding="utf-8")
        self.assertEqual(text.count("--exclude="), self.script.count("--exclude="))


class CargoHomeGuardTests(unittest.TestCase):
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


class PreparedCrateExtractionTests(unittest.TestCase):
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


class ModeTimeoutTests(unittest.TestCase):
    """Pin the per-mode limit table and the `timeout` re-exec guard."""

    LIMITS = {
        "ws-test": 5400,
        "audit": 5400,
        "installed-smoke": 5400,
        "guard-mutation": 5400,
        "clippy": 1800,
        "flake-eval": 1800,
        "ci-tests": 1800,
        "sandbox": 1800,
    }
    FUNCTIONS = ("check_timeout_secs", "report_sigterm", "reexec_under_timeout")
    # Each driver mode runs after the guard, standing in for a real mode.
    DRIVER_BODY = """
case "$1" in
  hang) sleep 60 ;;
  ignore-term) trap '' TERM; sleep 60 ;;
  exit7) exit 7 ;;
  self-kill) kill -USR1 "$$" ;;
  env)
    echo "active=${ANNEAL_CHECK_TIMEOUT_ACTIVE-unset}"
    echo "args=$*"
    ;;
esac
"""

    def limit(self, mode: str) -> int:
        text = SCRIPT.read_text(encoding="utf-8")
        result = subprocess.run(
            ["bash", "-euo", "pipefail", "-c",
             shell_function(text, "check_timeout_secs") + 'check_timeout_secs "$1"',
             "limit", mode],
            capture_output=True, text=True, check=True,
        )
        return int(result.stdout)

    def run_driver(self, args: list[str], *, kill_after: str = "120s",
                   env_extra: dict[str, str] | None = None,
                   ) -> subprocess.CompletedProcess[str]:
        text = SCRIPT.read_text(encoding="utf-8")
        functions = "".join(shell_function(text, name) for name in self.FUNCTIONS)
        self.assertIn("--kill-after=120s", functions)
        functions = functions.replace("--kill-after=120s", f"--kill-after={kill_after}")
        env = {k: v for k, v in os.environ.items()
               if not k.startswith("ANNEAL_CHECK_TIMEOUT")}
        env.update(env_extra or {})
        with tempfile.TemporaryDirectory() as tmp:
            driver = Path(tmp) / "driver.sh"
            driver.write_text(
                "#!/usr/bin/env bash\nset -euo pipefail\n" + functions
                + 'reexec_under_timeout "$@"\n' + self.DRIVER_BODY,
                encoding="utf-8",
            )
            return subprocess.run(
                ["bash", str(driver), *args], capture_output=True, text=True,
                env=env, timeout=50, check=False,
            )

    def test_limit_table(self) -> None:
        for mode, secs in self.LIMITS.items():
            with self.subTest(mode=mode):
                self.assertEqual(self.limit(mode), secs)
        self.assertEqual(self.limit("some-future-mode"), 1800)

    def test_every_dispatched_mode_has_explicit_limit(self) -> None:
        text = SCRIPT.read_text(encoding="utf-8")
        dispatch = text[text.index('\ncase "$MODE" in\n'):]
        modes = set(re.findall(r"^  ([a-z][a-z-]*)\)$", dispatch, re.M))
        self.assertEqual(modes, set(self.LIMITS))
        table = shell_function(text, "check_timeout_secs")
        for mode in modes:
            with self.subTest(mode=mode):
                self.assertRegex(table, rf"[ |]{re.escape(mode)}[|)]")

    def test_guard_runs_before_any_work(self) -> None:
        lines = SCRIPT.read_text(encoding="utf-8").splitlines()
        call = lines.index('reexec_under_timeout "$@"')
        self.assertEqual(lines.count('reexec_under_timeout "$@"'), 1)
        self.assertLess(call, lines.index('MODE="$1"'))
        self.assertLess(call, next(i for i, line in enumerate(lines)
                                   if line.startswith("cd ")))

    def test_guard_execs_timeout_with_kill_after(self) -> None:
        guard = shell_function(SCRIPT.read_text(encoding="utf-8"),
                               "reexec_under_timeout")
        self.assertIn(
            'exec /usr/bin/timeout --verbose --kill-after=120s "${limit}s" \\\n'
            '    "$BASH" "$0" "$@"',
            guard,
        )

    def test_timeout_exits_124_with_clear_message(self) -> None:
        result = self.run_driver(["hang"], env_extra={"ANNEAL_CHECK_TIMEOUT_SECS": "1"})
        self.assertEqual(result.returncode, 124, result.stderr)
        self.assertIn("hang: limit 1s", result.stderr)
        self.assertIn("timeout: sending signal TERM", result.stderr)
        self.assertIn("error: run_anneal_check.sh hang got SIGTERM: its 1s limit",
                      result.stderr)

    def test_term_ignoring_mode_is_killed(self) -> None:
        result = self.run_driver(["ignore-term"], kill_after="1s",
                                 env_extra={"ANNEAL_CHECK_TIMEOUT_SECS": "1"})
        # `timeout` kills its own process group, itself included, so a shell
        # parent sees status 137 and Python sees death by SIGKILL.
        self.assertIn(result.returncode, (137, -9), result.stderr)
        self.assertIn("timeout: sending signal KILL", result.stderr)

    def test_exit_status_and_signal_pass_through(self) -> None:
        result = self.run_driver(["exit7"])
        self.assertEqual(result.returncode, 7, result.stderr)
        result = self.run_driver(["self-kill"])
        self.assertIn(result.returncode, (128 + 10, -10), result.stderr)

    def test_sentinel_is_cleared_and_args_preserved(self) -> None:
        result = self.run_driver(["env", "a b", "c"])
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, "active=unset\nargs=env a b c\n")

    def test_override_may_only_tighten(self) -> None:
        for value in ("1801", "0", "-1", "1e3", "abc", "9999999"):
            with self.subTest(value=value):
                result = self.run_driver(
                    ["exit7"], env_extra={"ANNEAL_CHECK_TIMEOUT_SECS": value})
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn("ANNEAL_CHECK_TIMEOUT_SECS must be in 1..1800",
                              result.stderr)


if __name__ == "__main__":
    unittest.main()
