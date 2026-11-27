# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Exercise Anneal ci-core workflow, manifest, sandbox, and cache invariants."""

# The test methods live in mixins in the `ci_workflow_tests` package, one
# module per domain. Each test class here combines its mixins with
# `unittest.TestCase`, so every test keeps its `module.Class.method` ID and
# `unittest` discovery, which loads only `test_*.py` files, runs it once.

from pathlib import Path
import sys
import tomllib
import unittest

_CI_DIR = str(Path(__file__).resolve().parent)
if _CI_DIR not in sys.path:
    sys.path.insert(0, _CI_DIR)

from ci_workflow_tests.ci_core_workflows import CiCoreWorkflowCases
from ci_workflow_tests.manifest_guard import ManifestGuardCases
from ci_workflow_tests.pr_hygiene_workflow import PrHygieneWorkflowCases
from ci_workflow_tests.smoke_and_spec import SmokeAndSpecCases
from ci_workflow_tests.support import (
    extract_bash_function,
    load_workflow_yaml,
    REPO_ROOT,
    SOURCE,
)


class CiWorkflowManifestGuardTests(
    CiCoreWorkflowCases,
    ManifestGuardCases,
    SmokeAndSpecCases,
    unittest.TestCase,
):
    @classmethod
    def setUpClass(cls):
        cls.runner_script = (SOURCE / "run_anneal_check.sh").read_text()
        cls.pack_script = (SOURCE / "pack_omnibus_archive.sh").read_text()
        cls.manifest_fn = extract_bash_function(
            cls.runner_script, "verify_root_tcb_manifest"
        )
        cls.bundle_env_fn = extract_bash_function(
            cls.runner_script, "apply_bundle_env"
        )
        cls.checks_cfg = tomllib.loads(
            (REPO_ROOT / "ci/checks.toml").read_text()
        )
        cls.pr_wf = load_workflow_yaml(
            (REPO_ROOT / ".github/workflows/ci-core-pr.yml").read_text()
        )
        cls.trusted_wf = load_workflow_yaml(
            (REPO_ROOT / ".github/workflows/ci-core-trusted.yml").read_text()
        )
        cls.codeowners = (REPO_ROOT / ".github/CODEOWNERS").read_text()


class PrHygieneWorkflowTests(PrHygieneWorkflowCases, unittest.TestCase):
    pass


if __name__ == "__main__":
    unittest.main()
