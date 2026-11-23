# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for the `timeout` re-exec guard in ci/scripts/run_*.sh."""

import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest


REPO_ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = REPO_ROOT / "ci" / "scripts"

# Wall-clock limit in seconds for each check entrypoint.
LIMITS = {
    "run_anneal_mir_eval_check.sh": 1800,
    "run_anneal_spec_check.sh": 1800,
    "run_exocrate_test.sh": 1800,
    "run_fmt_domain.sh": 1800,
    "run_meta_actions.sh": 1800,
    "run_zc_build_test.sh": 1800,
    "run_zc_codegen.sh": 1800,
    "run_zc_cross_special.sh": 1800,
    "run_zc_kani.sh": 1080,
    "run_zc_miri.sh": 2700,
    "run_zc_semver.sh": 1800,
}

GUARD_RE = re.compile(
    r"^TIMEOUT_SECS=(?P<secs>[0-9]+)\n"
    r"(?P<body>if \[\[ -z .*?\nfi\nunset CI_SCRIPT_TIMEOUT_ACTIVE\n)",
    re.M | re.S,
)
EXPECTED_BODY = """\
if [[ -z "${CI_SCRIPT_TIMEOUT_ACTIVE:-}" ]]; then
  echo "$0: limit ${TIMEOUT_SECS}s; exit 124 or 137 means it timed out" >&2
  export CI_SCRIPT_TIMEOUT_ACTIVE=1
  exec /usr/bin/timeout --verbose --kill-after=120s "${TIMEOUT_SECS}s" \\
    "$BASH" "$0" "$@"
fi
unset CI_SCRIPT_TIMEOUT_ACTIVE
"""


def guard(script: Path) -> re.Match[str]:
    match = GUARD_RE.search(script.read_text(encoding="utf-8"))
    if match is None:
        raise AssertionError(f"{script.name}: timeout guard not found")
    return match


class ScriptTimeoutTests(unittest.TestCase):
    def test_every_entrypoint_has_pinned_limit(self) -> None:
        names = {p.name for p in SCRIPTS.glob("run_*.sh")}
        self.assertEqual(names, set(LIMITS))
        for name, secs in LIMITS.items():
            with self.subTest(script=name):
                match = guard(SCRIPTS / name)
                self.assertEqual(int(match.group("secs")), secs)
                self.assertEqual(match.group("body"), EXPECTED_BODY)

    def test_guard_precedes_all_other_commands(self) -> None:
        for name in LIMITS:
            with self.subTest(script=name):
                text = (SCRIPTS / name).read_text(encoding="utf-8")
                head = text[:guard(SCRIPTS / name).start()]
                code = [line for line in head.splitlines()
                        if line.strip() and not line.startswith("#")]
                self.assertEqual(code, ["set -euo pipefail"])

    def run_driver(self, body: str, secs: int, *args: str,
                   kill_after: str = "120s") -> subprocess.CompletedProcess[str]:
        block = guard(SCRIPTS / "run_zc_miri.sh").group(0)
        block = re.sub(r"^TIMEOUT_SECS=[0-9]+", f"TIMEOUT_SECS={secs}", block,
                       flags=re.M)
        block = block.replace("--kill-after=120s", f"--kill-after={kill_after}")
        env = {k: v for k, v in os.environ.items()
               if k != "CI_SCRIPT_TIMEOUT_ACTIVE"}
        with tempfile.TemporaryDirectory() as tmp:
            driver = Path(tmp) / "driver.sh"
            driver.write_text(
                "#!/usr/bin/env bash\nset -euo pipefail\n" + block + body,
                encoding="utf-8",
            )
            return subprocess.run(
                ["bash", str(driver), *args], capture_output=True, text=True,
                env=env, timeout=50, check=False,
            )

    def test_timeout_exits_124(self) -> None:
        result = self.run_driver("sleep 60\n", 1)
        self.assertEqual(result.returncode, 124, result.stderr)
        self.assertIn("limit 1s; exit 124 or 137", result.stderr)
        self.assertIn("timeout: sending signal TERM", result.stderr)

    def test_term_ignoring_script_is_killed(self) -> None:
        result = self.run_driver("trap '' TERM\nsleep 60\n", 1, kill_after="1s")
        # `timeout` kills its own process group, itself included, so a shell
        # parent sees status 137 and Python sees death by SIGKILL.
        self.assertIn(result.returncode, (137, -9), result.stderr)
        self.assertIn("timeout: sending signal KILL", result.stderr)

    def test_status_args_and_sentinel_pass_through(self) -> None:
        result = self.run_driver(
            'echo "active=${CI_SCRIPT_TIMEOUT_ACTIVE-unset} args=$*"\nexit 7\n',
            30, "a b", "c",
        )
        self.assertEqual(result.returncode, 7, result.stderr)
        self.assertEqual(result.stdout, "active=unset args=a b c\n")


if __name__ == "__main__":
    unittest.main()
