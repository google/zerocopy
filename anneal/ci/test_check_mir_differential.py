#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `ci/check_mir_differential.py`."""

# The test methods live in the `check_mir_differential_tests` package, grouped
# by domain into plain mixin classes. Composing them into
# `CheckMirDifferentialTests` here lets `unittest` discovery, which loads only
# `test_*.py` files, find each test exactly once under its original name.

from pathlib import Path
import sys
import unittest

_CI_DIR = str(Path(__file__).resolve().parent)
if _CI_DIR not in sys.path:
    sys.path.insert(0, _CI_DIR)
sys.dont_write_bytecode = True

from check_mir_differential_tests.paths_and_env import PathsAndEnvCases
from check_mir_differential_tests.report_and_eval import ReportAndEvalCases
from check_mir_differential_tests.workspace_selection import (
    WorkspaceSelectionCases,
)


class CheckMirDifferentialTests(
    ReportAndEvalCases,
    PathsAndEnvCases,
    WorkspaceSelectionCases,
    unittest.TestCase,
):
    pass


if __name__ == "__main__":
    unittest.main()
