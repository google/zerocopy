# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for the parallel Python CI test runner `anneal/ci/run_py_tests.py`."""

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

import run_py_tests


RUNNER = Path(__file__).resolve().parent / "run_py_tests.py"


class RunPyTestsTests(unittest.TestCase):
    def invoke(self, *args: str, cwd: Path | None = None) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, "-B", str(RUNNER), *args],
            cwd=cwd,
            capture_output=True,
            text=True,
            check=False,
        )

    def test_discovery_finds_top_level_and_subpackage_modules(self):
        with tempfile.TemporaryDirectory(prefix="anneal-run-py-disc-") as tmp:
            root = Path(tmp)
            (root / "test_alpha.py").write_text("import unittest\n", encoding="utf-8")
            (root / "helper.py").write_text("X = 1\n", encoding="utf-8")
            pkg = root / "subpkg"
            pkg.mkdir()
            (pkg / "__init__.py").write_text("", encoding="utf-8")
            (pkg / "test_beta.py").write_text("import unittest\n", encoding="utf-8")
            # Non-package directory without `__init__.py` must be skipped.
            non_pkg = root / "fixtures"
            non_pkg.mkdir()
            (non_pkg / "test_ignored.py").write_text("import unittest\n", encoding="utf-8")

            discovered = run_py_tests.discover_test_modules(root, "test_*.py")
            names = {mod for mod, _ in discovered}
            self.assertEqual(names, {"test_alpha", "subpkg.test_beta"})

    def test_parallel_pass_aggregates_counts_and_skips(self):
        with tempfile.TemporaryDirectory(prefix="anneal-run-py-pass-") as tmp:
            root = Path(tmp)
            (root / "test_one.py").write_text(
                "import unittest\n"
                "class OneTests(unittest.TestCase):\n"
                "    def test_a(self): self.assertEqual(1 + 1, 2)\n"
                "    def test_b(self): self.assertTrue(True)\n",
                encoding="utf-8",
            )
            (root / "test_two.py").write_text(
                "import unittest\n"
                "class TwoTests(unittest.TestCase):\n"
                "    def test_c(self): self.assertEqual(2 * 3, 6)\n"
                "    @unittest.skip('expected skip')\n"
                "    def test_skip(self): pass\n",
                encoding="utf-8",
            )
            res = self.invoke("--start-dir", str(root), "--jobs", "2", "--verbose")
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            self.assertIn("Ran 4 tests across 2/2 modules", res.stdout)
            self.assertIn("OK (failures=0, errors=0, skipped=1)", res.stdout)
            # Confirm `-B` avoided creating `__pycache__` inside the test dir.
            self.assertFalse((root / "__pycache__").exists())

    def test_failure_and_import_error_propagate_nonzero(self):
        with tempfile.TemporaryDirectory(prefix="anneal-run-py-fail-") as tmp:
            root = Path(tmp)
            (root / "test_ok.py").write_text(
                "import unittest\n"
                "class OkTests(unittest.TestCase):\n"
                "    def test_ok(self): pass\n",
                encoding="utf-8",
            )
            (root / "test_fail.py").write_text(
                "import unittest\n"
                "class FailTests(unittest.TestCase):\n"
                "    def test_boom(self): self.assertEqual(1, 2)\n",
                encoding="utf-8",
            )
            (root / "test_broken_import.py").write_text(
                "import nonexistent_module_xyz_12345\n",
                encoding="utf-8",
            )
            res = self.invoke("--start-dir", str(root), "--jobs", "3")
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("FAILED", res.stderr)
            self.assertIn("failures=1", res.stderr)
            self.assertIn("errors=1", res.stderr)
            self.assertIn("test_fail", res.stderr)
            self.assertIn("test_broken_import", res.stderr)

    def test_zero_discovered_modules_fails_closed(self):
        with tempfile.TemporaryDirectory(prefix="anneal-run-py-empty-") as tmp:
            res = self.invoke("--start-dir", tmp, "--pattern", "test_*.py")
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("No test modules", res.stderr)

    def test_zero_executed_tests_in_discovered_module_fails_closed(self):
        with tempfile.TemporaryDirectory(prefix="anneal-run-py-zero-") as tmp:
            root = Path(tmp)
            (root / "test_empty.py").write_text("X = 42\n", encoding="utf-8")
            res = self.invoke("--start-dir", str(root), "--jobs", "1")
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("0 tests were executed", res.stderr)

    def test_failfast_exits_nonzero_on_failure(self):
        with tempfile.TemporaryDirectory(prefix="anneal-run-py-ff-") as tmp:
            root = Path(tmp)
            (root / "test_failfast.py").write_text(
                "import unittest\n"
                "class FFTests(unittest.TestCase):\n"
                "    def test_1_fail(self): self.fail('first')\n"
                "    def test_2_fail(self): self.fail('second')\n",
                encoding="utf-8",
            )
            res = self.invoke("--start-dir", str(root), "--jobs", "1", "--failfast")
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("failures=1", res.stderr)

    def test_spoofed_stdout_and_os_exit_zero_fails_closed(self):
        with tempfile.TemporaryDirectory(prefix="anneal-run-py-spoof-") as tmp:
            root = Path(tmp)
            (root / "test_spoof.py").write_text(
                "import json, os, sys, unittest\n"
                "class SpoofTests(unittest.TestCase):\n"
                "    def test_forge(self):\n"
                "        fake = {\n"
                "            'module': 'test_spoof', 'tests_run': 1, 'failures': 0,\n"
                "            'errors': 0, 'skipped': 0, 'expected_failures': 0,\n"
                "            'unexpected_successes': 0, 'was_successful': True,\n"
                "            'duration_sec': 0.01,\n"
                "        }\n"
                "        sys.stdout.write('\\n__ANNEAL_PY_TEST_RESULT_JSON__:' + json.dumps(fake) + '\\n')\n"
                "        sys.stdout.flush()\n"
                "        os._exit(0)\n",
                encoding="utf-8",
            )
            res = self.invoke("--start-dir", str(root), "--jobs", "1")
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("without writing a structured result", res.stderr)
            self.assertIn("errors=1", res.stderr)

    def test_module_timeout_kills_hung_worker_and_fails_closed(self):
        with tempfile.TemporaryDirectory(prefix="anneal-run-py-timeout-") as tmp:
            root = Path(tmp)
            (root / "test_hang.py").write_text(
                "import time, unittest\n"
                "class HangTests(unittest.TestCase):\n"
                "    def test_hang(self):\n"
                "        time.sleep(30)\n",
                encoding="utf-8",
            )
            res = self.invoke(
                "--start-dir",
                str(root),
                "--jobs",
                "1",
                "--module-timeout",
                "0.4",
            )
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("timed out", res.stderr)
            self.assertIn("errors=1", res.stderr)

    def test_module_timeout_kills_grandchild_process_group_promptly(self):
        with tempfile.TemporaryDirectory(prefix="anneal-run-py-pg-") as tmp:
            root = Path(tmp)
            (root / "test_hang_child.py").write_text(
                "import subprocess, sys, unittest\n"
                "class HangChildTests(unittest.TestCase):\n"
                "    def test_hang_child(self):\n"
                "        subprocess.run([sys.executable, '-c', 'import time; time.sleep(40)'], check=False)\n",
                encoding="utf-8",
            )
            t0 = time.monotonic()
            res = self.invoke(
                "--start-dir",
                str(root),
                "--jobs",
                "1",
                "--module-timeout",
                "0.5",
            )
            elapsed = time.monotonic() - t0
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("timed out", res.stderr)
            self.assertIn("errors=1", res.stderr)
            self.assertLess(
                elapsed,
                5.0,
                f"Expected hung grandchild to be killed promptly, took {elapsed:.2f}s",
            )

    def test_grandchild_does_not_inherit_result_fd_and_stall_parent(self):
        with tempfile.TemporaryDirectory(prefix="anneal-run-py-noinh-") as tmp:
            root = Path(tmp)
            (root / "test_bg_child.py").write_text(
                "import subprocess, sys, unittest\n"
                "class BgChildTests(unittest.TestCase):\n"
                "    def test_spawn_detached_sleeper(self):\n"
                "        subprocess.Popen(\n"
                "            [sys.executable, '-c', 'import time; time.sleep(4)'],\n"
                "            stdin=subprocess.DEVNULL,\n"
                "            stdout=subprocess.DEVNULL,\n"
                "            stderr=subprocess.DEVNULL,\n"
                "            start_new_session=True,\n"
                "        )\n",
                encoding="utf-8",
            )
            t0 = time.monotonic()
            res = self.invoke(
                "--start-dir",
                str(root),
                "--jobs",
                "1",
                "--module-timeout",
                "10",
            )
            elapsed = time.monotonic() - t0
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            self.assertLess(
                elapsed,
                2.5,
                f"Expected result_fd non-inheritance to return promptly, took {elapsed:.2f}s",
            )

    def test_failfast_does_not_submit_remaining_modules_after_first_failure(self):
        with tempfile.TemporaryDirectory(prefix="anneal-run-py-ffq-") as tmp:
            root = Path(tmp)
            marker_2 = root / "ran_2.marker"
            marker_3 = root / "ran_3.marker"
            # Pad `test_1_fail.py` with comments so LPT schedules it first.
            pad = "# " + ("x" * 400) + "\n"
            (root / "test_1_fail.py").write_text(
                pad
                + "import unittest\n"
                "class FirstFail(unittest.TestCase):\n"
                "    def test_fail(self): self.fail('boom')\n",
                encoding="utf-8",
            )
            (root / "test_2_never.py").write_text(
                "from pathlib import Path\nimport unittest\n"
                f"Path({str(marker_2)!r}).write_text('ran', encoding='utf-8')\n"
                "class Second(unittest.TestCase):\n"
                "    def test_ok(self): pass\n",
                encoding="utf-8",
            )
            (root / "test_3_never.py").write_text(
                "from pathlib import Path\nimport unittest\n"
                f"Path({str(marker_3)!r}).write_text('ran', encoding='utf-8')\n"
                "class Third(unittest.TestCase):\n"
                "    def test_ok(self): pass\n",
                encoding="utf-8",
            )
            res = self.invoke("--start-dir", str(root), "--jobs", "1", "--failfast")
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("failfast=stopped", res.stderr)
            self.assertIn("across 1/3 modules", res.stderr)
            self.assertFalse(marker_2.exists(), "test_2_never should not have been submitted")
            self.assertFalse(marker_3.exists(), "test_3_never should not have been submitted")

    def test_worker_runs_in_isolated_mode_ignoring_pythonpath(self):
        with tempfile.TemporaryDirectory(prefix="anneal-run-py-iso-") as tmp:
            root = Path(tmp) / "tests"
            poison = Path(tmp) / "poison"
            root.mkdir()
            poison.mkdir()
            (poison / "poison_mod.py").write_text("X = 1\n", encoding="utf-8")
            (root / "test_iso.py").write_text(
                "import sys, unittest\n"
                "class IsoTests(unittest.TestCase):\n"
                "    def test_isolated_flag_and_no_pythonpath(self):\n"
                "        self.assertEqual(sys.flags.isolated, 1)\n"
                "        with self.assertRaises(ModuleNotFoundError):\n"
                "            import poison_mod  # noqa: F401\n",
                encoding="utf-8",
            )
            env = os.environ.copy()
            env["PYTHONPATH"] = str(poison)
            res = subprocess.run(
                [sys.executable, "-B", str(RUNNER), "--start-dir", str(root), "--jobs", "1"],
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            self.assertIn("Ran 1 tests across 1/1 modules", res.stdout)

    def test_nonpositive_module_timeout_rejected(self):
        with tempfile.TemporaryDirectory(prefix="anneal-run-py-badto-") as tmp:
            for bad in ("0", "-5", "nan", "inf", "-inf"):
                res = self.invoke("--start-dir", tmp, "--module-timeout", bad)
                self.assertEqual(res.returncode, 2, bad)
                self.assertIn("--module-timeout", res.stderr)


if __name__ == "__main__":
    unittest.main()
