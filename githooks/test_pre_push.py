#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Regression tests for pre-push child and lockfile accounting."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


_ROOT = Path(__file__).resolve().parents[1]
_HOOK = _ROOT / "githooks" / "pre-push"
_LOCKFILES = (
    "anneal/Cargo.lock",
    "anneal/v1/Cargo.lock",
    "exocrate/Cargo.lock",
    "tools/Cargo.lock",
    "zerocopy/Cargo.lock",
)
_CHECKS = (
    "ci/check_actions.sh",
    "ci/check_fmt.sh",
    "ci/check_job_dependencies.sh",
    "zerocopy/ci/check_all_toolchains_tested.sh",
    "zerocopy/ci/check_readme.sh",
    "zerocopy/ci/check_stale_stderr.sh",
    "zerocopy/ci/check_versions.sh",
    "zerocopy/ci/check_msrv_is_minimal.sh",
)
_EXEMPT_RELEASE_HELPERS = (
    "ci/run_cargo_for_release.sh",
    "zerocopy/ci/package_release_crates.sh",
)

_CHECK_STUB = """\
#!/usr/bin/env bash
set -eu
check=${0#./}
if [[ "$check" == "${MUTATING_CHECK:-}" ]]; then
    echo mutation >> "$MUTATE_LOCKFILE"
fi
if [[ "$check" == "${DELETING_CHECK:-}" ]]; then
    rm -f "$DELETE_LOCKFILE"
fi
if [[ "$check" == "${SLOW_CHECK:-}" ]]; then
    sleep 0.2
fi
touch "$MARKER_DIR/${check//\\//_}"
if [[ "$check" == "${FAIL_CHECK:-}" ]]; then
    exit 23
fi
"""

_CARGO_STUB = """\
#!/usr/bin/env bash
set -eu
invocation="$*"
if ! mkdir "$MARKER_DIR/cargo_bootstrap_lock"; then
    echo "concurrent cargo bootstrap" >&2
    exit 42
fi
trap 'rmdir "$MARKER_DIR/cargo_bootstrap_lock"' EXIT
printf '%s\\n' "$invocation" >> "$MARKER_DIR/cargo_invocations"
if [[ "$invocation" == "${MUTATING_CARGO_INVOCATION:-}" ]]; then
    echo mutation >> "$MUTATE_LOCKFILE"
fi
sleep 0.05
if [[ "$invocation" == "${FAIL_CARGO_INVOCATION:-}" ]]; then
    exit 23
fi
"""


class FakeRepository:
    def __init__(self):
        self._temporary_directory = tempfile.TemporaryDirectory()
        self.path = Path(self._temporary_directory.name)
        self.markers = self.path / "markers"

        (self.path / "githooks").mkdir()
        self.markers.mkdir()
        shutil.copy2(_HOOK, self.path / "githooks" / "pre-push")

        for lockfile in _LOCKFILES:
            path = self.path / lockfile
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(f"original {lockfile}\n", encoding="utf-8")

        # The hook deliberately excludes checked-in dependency and fixture
        # lockfiles from its first-party workspace inventory.
        for lockfile in (
            "zerocopy/vendor/example/Cargo.lock",
            "anneal/v1/tests/fixtures/example/Cargo.lock",
        ):
            path = self.path / lockfile
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("source snapshot\n", encoding="utf-8")

        for check in _CHECKS:
            path = self.path / check
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(_CHECK_STUB, encoding="utf-8")
            path.chmod(0o755)

        # These helpers are deliberately inventoried but not executed by the
        # read-only hook. Their presence catches drift in its GLOBIGNORE
        # contract without invoking publication-oriented behavior in a test.
        for helper in _EXEMPT_RELEASE_HELPERS:
            path = self.path / helper
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("#!/usr/bin/env bash\nexit 99\n", encoding="utf-8")
            path.chmod(0o755)

        cargo = self.path / "zerocopy/cargo.sh"
        cargo.write_text(_CARGO_STUB, encoding="utf-8")
        cargo.chmod(0o755)

        subprocess.run(
            ["git", "init", "--quiet"], cwd=self.path, check=True
        )
        subprocess.run(
            ["git", "add", "."], cwd=self.path, check=True
        )

    def close(self):
        self._temporary_directory.cleanup()

    def run_hook(self, start_directory=".", **environment):
        child_environment = os.environ.copy()
        child_environment.update(environment)
        child_environment["MARKER_DIR"] = str(self.markers)
        return subprocess.run(
            ["bash", str(self.path / "githooks" / "pre-push")],
            cwd=self.path / start_directory,
            env=child_environment,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )


class PrePushTest(unittest.TestCase):
    def setUp(self):
        self.repository = FakeRepository()

    def tearDown(self):
        self.repository.close()

    def cargo_invocations(self):
        return (
            self.repository.markers / "cargo_invocations"
        ).read_text(encoding="utf-8").splitlines()

    def test_bootstraps_serially_and_leaves_every_lockfile_unchanged(self):
        result = self.repository.run_hook()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(
            self.cargo_invocations(),
            ["+stable --version", "+nightly --version"],
        )
        for check in _CHECKS:
            self.assertTrue(
                (self.repository.markers / check.replace("/", "_")).is_file()
            )

    def test_can_run_from_a_repository_subdirectory(self):
        result = self.repository.run_hook(start_directory="zerocopy")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_bootstrap_failure_still_guards_lockfiles(self):
        lockfile = _LOCKFILES[-1]
        result = self.repository.run_hook(
            FAIL_CARGO_INVOCATION="+stable --version",
            MUTATING_CARGO_INVOCATION="+stable --version",
            MUTATE_LOCKFILE=str(self.repository.path / lockfile),
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(
            "zerocopy/cargo.sh +stable --version failed with status 23",
            result.stderr,
        )
        self.assertIn(f"{lockfile} was modified", result.stderr)
        self.assertEqual(
            self.cargo_invocations(),
            ["+stable --version", "+nightly --version"],
        )
        for check in _CHECKS:
            self.assertFalse(
                (self.repository.markers / check.replace("/", "_")).exists()
            )

    def test_each_first_party_lockfile_is_guarded_against_changes(self):
        for operation in ("mutate", "delete"):
            for lockfile in _LOCKFILES:
                with self.subTest(operation=operation, lockfile=lockfile):
                    self.repository.close()
                    self.repository = FakeRepository()
                    environment = (
                        {
                            "MUTATING_CHECK": "ci/check_actions.sh",
                            "MUTATE_LOCKFILE": str(self.repository.path / lockfile),
                        }
                        if operation == "mutate"
                        else {
                            "DELETING_CHECK": "ci/check_actions.sh",
                            "DELETE_LOCKFILE": str(self.repository.path / lockfile),
                        }
                    )
                    result = self.repository.run_hook(**environment)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn(
                        f"{lockfile} was modified by a nominally read-only",
                        result.stderr,
                    )

    def test_allows_preexisting_dirty_or_missing_lockfile(self):
        lockfile = self.repository.path / _LOCKFILES[0]
        lockfile.write_text("preexisting local edit\n", encoding="utf-8")
        result = self.repository.run_hook()
        self.assertEqual(result.returncode, 0, result.stderr)

        self.repository.close()
        self.repository = FakeRepository()
        (self.repository.path / _LOCKFILES[0]).unlink()
        result = self.repository.run_hook()
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_waits_for_every_child_after_an_early_failure(self):
        slow_check = "zerocopy/ci/check_msrv_is_minimal.sh"
        lockfile = _LOCKFILES[-1]
        result = self.repository.run_hook(
            FAIL_CHECK="ci/check_actions.sh",
            SLOW_CHECK=slow_check,
            MUTATING_CHECK=slow_check,
            MUTATE_LOCKFILE=str(self.repository.path / lockfile),
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("ci/check_actions.sh failed with status 23", result.stderr)
        self.assertIn(f"{lockfile} was modified", result.stderr)
        self.assertTrue((self.repository.markers / slow_check.replace("/", "_")).is_file())

    def test_reports_a_non_first_child_failure(self):
        failed_check = "zerocopy/ci/check_stale_stderr.sh"
        result = self.repository.run_hook(FAIL_CHECK=failed_check)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(f"{failed_check} failed with status 23", result.stderr)


if __name__ == "__main__":
    unittest.main()
