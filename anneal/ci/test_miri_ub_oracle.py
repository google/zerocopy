# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for the 2-tier Miri UB oracle harness."""

# The test methods live in the `miri_ub_oracle_tests` package, grouped by
# domain into plain mixin classes. Composing them into the five `TestCase`
# classes here lets `unittest` discovery, which loads only `test_*.py`
# files, find each test exactly once under its original class and method
# names.

from pathlib import Path
import sys
import unittest

_CI_DIR = str(Path(__file__).resolve().parent)
if _CI_DIR not in sys.path:
    sys.path.insert(0, _CI_DIR)

from miri_ub_oracle_tests.bounded_runs_and_tier_b import BoundedRunAndTierBCases
from miri_ub_oracle_tests.capture_hardening import CaptureHardeningCases
from miri_ub_oracle_tests.capture_pdeathsig import CapturePdeathsigCases
from miri_ub_oracle_tests.child_env_and_symlinks import ChildEnvAndSymlinkCases
from miri_ub_oracle_tests.classification import ClassificationCases
from miri_ub_oracle_tests.corpus_manifest import CorpusManifestCases
from miri_ub_oracle_tests.pin_and_tar import PinAndSupplyChainCases
from miri_ub_oracle_tests.pin_and_tar import SafeTarExtractionCases
from miri_ub_oracle_tests.preexec_confinement import PreexecConfinementCases
from miri_ub_oracle_tests.stubbed_end_to_end import StubbedEndToEndCases


class PinAndSupplyChainTests(
    PinAndSupplyChainCases,
    unittest.TestCase,
):
    pass


class SafeTarExtractionTests(
    SafeTarExtractionCases,
    unittest.TestCase,
):
    pass


class ClassificationAndGateTests(
    ClassificationCases,
    PreexecConfinementCases,
    BoundedRunAndTierBCases,
    unittest.TestCase,
):
    pass


class StubbedEndToEndTests(
    StubbedEndToEndCases,
    unittest.TestCase,
):
    pass


class RealTierBCorpusHygieneTests(
    CorpusManifestCases,
    ChildEnvAndSymlinkCases,
    CapturePdeathsigCases,
    CaptureHardeningCases,
    unittest.TestCase,
):
    pass


if __name__ == "__main__":
    unittest.main()
