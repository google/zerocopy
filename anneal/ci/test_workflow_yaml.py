# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Exercise workflow YAML decoding and supply-chain/policy checks."""

# The test methods live in the `workflow_yaml_tests` package, grouped by
# domain into plain mixin classes. Composing them into `WorkflowYamlTests`
# and `WorkflowPolicyLintTests` here lets `unittest` discovery, which loads
# only `test_*.py` files, find each test exactly once under its original
# class and method names.

from pathlib import Path
import sys
import unittest

_CI_DIR = str(Path(__file__).resolve().parent)
if _CI_DIR not in sys.path:
    sys.path.insert(0, _CI_DIR)

from workflow_yaml_tests.env_and_artifacts import EnvAndArtifactCases
from workflow_yaml_tests.mounted_trees import MountedTreeCases
from workflow_yaml_tests.pinned_downloads import PinnedDownloadCases
from workflow_yaml_tests.yaml_decoding import YamlDecodingCases


class WorkflowYamlTests(YamlDecodingCases, unittest.TestCase):
    pass


class WorkflowPolicyLintTests(
    EnvAndArtifactCases,
    PinnedDownloadCases,
    MountedTreeCases,
    unittest.TestCase,
):
    pass


if __name__ == "__main__":
    unittest.main()
