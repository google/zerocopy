# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Tests of the per-mode `timeout` guard in `run_anneal_check.sh`."""

import os
from pathlib import Path
import re
import subprocess
import tempfile

from run_anneal_check_tests.support import SCRIPT, shell_function


class ModeTimeoutCases:
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
        "ws-meta": 1800,
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
