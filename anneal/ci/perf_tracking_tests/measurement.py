# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Subprocess time and RSS measurement tests for `perf_tracking.py`."""

from __future__ import annotations

from pathlib import Path
import stat
import sys
import tempfile

import perf_tracking


class SubprocessMeasurementCases:
    def test_mock_usr_bin_time_wrapper_parses_maxrss(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fake_time = root / "time"
            fake_time.write_text(
                "#!/usr/bin/env python3\n"
                "import pathlib, subprocess, sys\n"
                "args = sys.argv[1:]\n"
                "out = pathlib.Path(args[args.index('-o') + 1])\n"
                "sep = args.index('--')\n"
                "cmd = args[sep + 1:]\n"
                "res = subprocess.run(cmd)\n"
                "out.write_text('__ANNEAL_TIME_MAXRSS_KIB__=42192\\n')\n"
                "sys.exit(res.returncode)\n",
                encoding="utf-8",
            )
            fake_time.chmod(stat.S_IRWXU)
            meas = perf_tracking.run_measured_subprocess(
                [sys.executable, "-c", "print('hello')"],
                time_bin=fake_time,
            )
            self.assertEqual(meas.returncode, 0)
            self.assertEqual(meas.stdout.strip(), "hello")
            self.assertEqual(meas.maxrss_kib, 42192)
            self.assertEqual(meas.rss_method, "usr_bin_time")

    def test_fallback_fork_wait4_when_time_absent(self):
        meas = perf_tracking.run_measured_subprocess(
            [sys.executable, "-c", "print('ok')"],
            time_bin=None,
        )
        self.assertEqual(meas.returncode, 0)
        self.assertEqual(meas.stdout.strip(), "ok")
        self.assertEqual(meas.rss_method, "fallback_wait4")
        self.assertGreater(meas.maxrss_kib, 0)

    def test_real_usr_bin_time_isolates_small_child_rss(self):
        time_bin = Path("/usr/bin/time")
        true_bin = Path("/bin/true")
        if not (
            sys.platform.startswith("linux")
            and time_bin.is_file()
            and true_bin.is_file()
        ):
            self.skipTest("Linux /usr/bin/time or /bin/true unavailable")
        # Allocate 32 MiB transiently in Python parent so parent hiwater_rss
        # exceeds 32 MiB before spawning /bin/true.
        blob = bytearray(32 * 1024 * 1024)
        blob[0] = 1
        del blob
        meas = perf_tracking.run_measured_subprocess(
            [str(true_bin)],
            time_bin=time_bin,
        )
        self.assertEqual(meas.returncode, 0)
        self.assertEqual(meas.rss_method, "usr_bin_time")
        self.assertLess(meas.maxrss_kib, 16384)
