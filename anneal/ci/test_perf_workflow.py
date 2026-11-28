# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Tests for `.github/workflows/anneal-perf.yml` and `.github/workflows/docs.yml`."""

# The test methods live in the `perf_workflow_tests` package, grouped by
# workflow into plain mixin classes. Composing them into the four `TestCase`
# classes here lets `unittest` discovery, which loads only `test_*.py`
# files, find each test exactly once under its original class and method
# names.

from pathlib import Path
import sys
import unittest

_CI_DIR = str(Path(__file__).resolve().parent)
if _CI_DIR not in sys.path:
    sys.path.insert(0, _CI_DIR)

from perf_workflow_tests.docs_workflow import DocsWorkflowExecutionCases
from perf_workflow_tests.docs_workflow import DocsWorkflowStaticCases
from perf_workflow_tests.perf_workflow import PerfWorkflowPublishExecutionCases
from perf_workflow_tests.perf_workflow import PerfWorkflowStaticCases


class PerfWorkflowStaticTests(
    PerfWorkflowStaticCases,
    unittest.TestCase,
):
    pass


class PerfWorkflowPublishExecutionTests(
    PerfWorkflowPublishExecutionCases,
    unittest.TestCase,
):
    pass


class DocsWorkflowStaticTests(
    DocsWorkflowStaticCases,
    unittest.TestCase,
):
    pass


class DocsWorkflowExecutionTests(
    DocsWorkflowExecutionCases,
    unittest.TestCase,
):
    pass


if __name__ == "__main__":
    unittest.main()
