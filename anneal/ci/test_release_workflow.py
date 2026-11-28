# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Audit Anneal release workflow triggers, privilege boundaries, and scripts."""

# The test methods live in mixins in the `release_workflow_tests` package,
# one module per domain. `ReleaseWorkflowTests` combines them, so every test
# keeps its `module.Class.method` ID and `unittest` discovery, which loads
# only `test_*.py` files, runs it exactly once.

from __future__ import annotations

from pathlib import Path
import sys
import unittest

_CI_DIR = str(Path(__file__).resolve().parent)
if _CI_DIR not in sys.path:
    sys.path.insert(0, _CI_DIR)

from release_workflow_tests.harness_and_staging import HarnessAndStagingCases
from release_workflow_tests.history_guards import HistoryGuardCases
from release_workflow_tests.release_contracts import ReleaseContractCases
from release_workflow_tests.support import load_workflow, WORKFLOWS
from release_workflow_tests.workflow_structure import WorkflowStructureCases


class ReleaseWorkflowTests(
    HarnessAndStagingCases,
    HistoryGuardCases,
    ReleaseContractCases,
    WorkflowStructureCases,
    unittest.TestCase,
):
    @classmethod
    def setUpClass(cls) -> None:
        cls.workflow = load_workflow(WORKFLOWS / "release.yml")
        cls.preparation = load_workflow(WORKFLOWS / "release-crate-version.yml")
        cls.jobs = cls.workflow["jobs"]


if __name__ == "__main__":
    unittest.main()
