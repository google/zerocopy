#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit and integration tests for `anneal/ci/anneal-lean-run`."""

# The test cases live in the `lean_run_tests` package, one module per
# class, each importing `setUpModule` and `tearDownModule` from
# `lean_run_tests.support` so that `unittest` runs the module fixture
# around every class. Importing them here lets `unittest` discovery,
# which loads only `test_*.py` files, find each test case exactly once.

from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True

_CI_DIR = str(Path(__file__).resolve().parent)
if _CI_DIR not in sys.path:
    sys.path.insert(0, _CI_DIR)

from lean_run_tests.caller_thread_count import TestCallerLoweredThreadCount
from lean_run_tests.cgroup_probing import TestCgroupV2Probing
from lean_run_tests.cli_and_limits import TestCliAndLimits
from lean_run_tests.cli_subprocess import TestCliSubprocess
from lean_run_tests.codex_p2_regressions import TestCodexP2Regressions
from lean_run_tests.platform_fallbacks import TestCrossPlatformAndNonSystemdFallback
from lean_run_tests.security_and_systemd import TestSecurityHardeningAndSystemdVersions
from lean_run_tests.watchdog_and_cpu_limits import TestWatchdogSignalsAndCpuLimits
from lean_run_tests.workload_memory import TestWorkloadMemoryEnvelope

__all__ = [
    "TestCallerLoweredThreadCount",
    "TestCgroupV2Probing",
    "TestCliAndLimits",
    "TestCliSubprocess",
    "TestCodexP2Regressions",
    "TestCrossPlatformAndNonSystemdFallback",
    "TestSecurityHardeningAndSystemdVersions",
    "TestWatchdogSignalsAndCpuLimits",
    "TestWorkloadMemoryEnvelope",
]


if __name__ == "__main__":
    unittest.main()
