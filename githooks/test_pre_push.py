#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Regression tests for pre-push bootstrap, children, and lockfile checks."""

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
    # Keep this fixture coordinated with the explicit fan-out in pre-push.
    # Omitting a real check here would leave its child handling untested.
    "ci/check_tools.sh",
    "zerocopy/ci/check_all_toolchains_tested.sh",
    "zerocopy/ci/check_readme.sh",
    "zerocopy/ci/check_stale_stderr.sh",
    "zerocopy/ci/check_versions.sh",
    "zerocopy/ci/check_msrv_is_minimal.sh",
)
_EXEMPT_CHECKS = (
    "ci/check_todo.sh",
    "ci/release_anneal_version.sh",
    "zerocopy/ci/check_fmt.sh",
    "zerocopy/ci/release_crate_version.sh",
)

_CHECK_STUB = """\
#!/usr/bin/env bash
set -eu
check=${0#./}
if [[ -n "${CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN:-}" ]]; then
    echo "bootstrap auto-install setting leaked into $check" >&2
    exit 24
fi
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
if [[ "${CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN:-}" != 1 ]]; then
    echo "bootstrap did not enable noninteractive auto-install" >&2
    exit 24
fi
if [[ "${PROBE_BOOTSTRAP_STDIN:-}" == 1 ]] && IFS= read -r line; then
    printf '%s\\n' "$line" > "$MARKER_DIR/bootstrap_stdin"
    echo "bootstrap consumed pre-push protocol input" >&2
    exit 25
fi
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
    """A minimal repository whose checks expose hook coordination bugs."""

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

        # Checked-in dependencies and fixtures have independent lockfiles and
        # are deliberately outside the first-party workspace contract.
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

        # These scripts are deliberately inventoried but exempt from direct
        # execution. Their presence tests the hook's exclusion contract.
        for check in _EXEMPT_CHECKS:
            path = self.path / check
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("#!/usr/bin/env bash\nexit 99\n", encoding="utf-8")
            path.chmod(0o755)

        cargo = self.path / "zerocopy/cargo.sh"
        cargo.write_text(_CARGO_STUB, encoding="utf-8")
        cargo.chmod(0o755)

        subprocess.run(
            ["git", "init", "--quiet"], cwd=self.path, check=True
        )
        subprocess.run(["git", "add", "."], cwd=self.path, check=True)

    def close(self):
        self._temporary_directory.cleanup()

    def run_hook(self, start_directory=".", **environment):
        child_environment = os.environ.copy()
        child_environment.pop(
            "CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN", None
        )
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

    def run_hook_then_capture_stdin(self, hook_input, **environment):
        child_environment = os.environ.copy()
        child_environment.pop(
            "CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN", None
        )
        child_environment.update(environment)
        child_environment["MARKER_DIR"] = str(self.markers)
        downstream_input = self.markers / "downstream_stdin"
        return subprocess.run(
            [
                "bash",
                "-c",
                'bash "$1"; status=$?; cat > "$2"; exit "$status"',
                "pre-push-test-wrapper",
                str(self.path / "githooks" / "pre-push"),
                str(downstream_input),
            ],
            cwd=self.path,
            env=child_environment,
            input=hook_input,
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

    def marker_for(self, check):
        return self.repository.markers / check.replace("/", "_")

    def test_bootstraps_serially_and_runs_every_check(self):
        result = self.repository.run_hook()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(
            self.cargo_invocations(),
            ["+stable --version", "+nightly --version"],
        )
        for check in _CHECKS:
            self.assertTrue(self.marker_for(check).is_file(), check)

    def test_bootstrap_preserves_protocol_input_for_later_hooks(self):
        protocol = (
            "refs/heads/main 1111111111111111111111111111111111111111 "
            "refs/heads/main 2222222222222222222222222222222222222222\n"
            "refs/heads/topic 3333333333333333333333333333333333333333 "
            "refs/heads/topic 4444444444444444444444444444444444444444\n"
        )
        result = self.repository.run_hook_then_capture_stdin(
            protocol, PROBE_BOOTSTRAP_STDIN="1"
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(
            (self.repository.markers / "bootstrap_stdin").exists()
        )
        self.assertEqual(
            (self.repository.markers / "downstream_stdin").read_text(
                encoding="utf-8"
            ),
            protocol,
        )

    def test_can_run_from_a_repository_subdirectory(self):
        result = self.repository.run_hook(start_directory="zerocopy")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_bootstrap_failure_still_checks_lockfiles(self):
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
            self.assertFalse(self.marker_for(check).exists(), check)

    def test_each_first_party_lockfile_is_guarded(self):
        for operation in ("mutate", "delete"):
            for lockfile in _LOCKFILES:
                with self.subTest(operation=operation, lockfile=lockfile):
                    self.repository.close()
                    self.repository = FakeRepository()
                    if operation == "mutate":
                        environment = {
                            "MUTATING_CHECK": "ci/check_actions.sh",
                            "MUTATE_LOCKFILE": str(
                                self.repository.path / lockfile
                            ),
                        }
                    else:
                        environment = {
                            "DELETING_CHECK": "ci/check_actions.sh",
                            "DELETE_LOCKFILE": str(
                                self.repository.path / lockfile
                            ),
                        }
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

    def test_ignores_source_snapshot_lockfiles(self):
        lockfile = self.repository.path / "zerocopy/vendor/example/Cargo.lock"
        result = self.repository.run_hook(
            MUTATING_CHECK="ci/check_actions.sh",
            MUTATE_LOCKFILE=str(lockfile),
        )
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
        self.assertIn(
            "ci/check_actions.sh failed with status 23", result.stderr
        )
        self.assertIn(f"{lockfile} was modified", result.stderr)
        self.assertTrue(self.marker_for(slow_check).is_file())

    def test_reports_a_non_first_child_failure(self):
        failed_check = "zerocopy/ci/check_stale_stderr.sh"
        result = self.repository.run_hook(FAIL_CHECK=failed_check)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(f"{failed_check} failed with status 23", result.stderr)


if __name__ == "__main__":
    unittest.main()
