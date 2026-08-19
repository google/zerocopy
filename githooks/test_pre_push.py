#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Regression tests for serialized pre-push toolchain bootstrap."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


_ROOT = Path(__file__).resolve().parents[1]
_HOOK = _ROOT / "githooks" / "pre-push"
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

_CHECK_STUB = """\
#!/usr/bin/env bash
set -eu
check=${0#./}
if [[ -n "${CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN:-}" ]]; then
    echo "bootstrap auto-install setting leaked into $check" >&2
    exit 24
fi
touch "$MARKER_DIR/${check//\\//_}"
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
printf '%s\n' "$invocation" >> "$MARKER_DIR/cargo_invocations"
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

        for check in _CHECKS:
            path = self.path / check
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(_CHECK_STUB, encoding="utf-8")
            path.chmod(0o755)

        cargo = self.path / "zerocopy/cargo.sh"
        cargo.write_text(_CARGO_STUB, encoding="utf-8")
        cargo.chmod(0o755)

    def close(self):
        self._temporary_directory.cleanup()

    def run_hook(self, **environment):
        child_environment = os.environ.copy()
        child_environment.pop(
            "CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN", None
        )
        child_environment.update(environment)
        child_environment["MARKER_DIR"] = str(self.markers)
        return subprocess.run(
            ["bash", str(self.path / "githooks" / "pre-push")],
            cwd=self.path,
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
        return (self.repository.markers / "cargo_invocations").read_text(
            encoding="utf-8"
        ).splitlines()

    def test_bootstraps_toolchains_serially_before_checks(self):
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

    def test_bootstrap_preserves_protocol_input_for_downstream_hooks(self):
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

    def test_bootstrap_failure_does_not_launch_parallel_checks(self):
        result = self.repository.run_hook(
            FAIL_CARGO_INVOCATION="+stable --version"
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(
            "zerocopy/cargo.sh +stable --version failed with status 23",
            result.stderr,
        )
        self.assertEqual(
            self.cargo_invocations(),
            ["+stable --version", "+nightly --version"],
        )
        for check in _CHECKS:
            self.assertFalse(
                (self.repository.markers / check.replace("/", "_")).exists()
            )


if __name__ == "__main__":
    unittest.main()
