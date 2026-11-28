# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit and behavioral tests for `run_anneal_check.sh` and `pack_omnibus_archive.sh`.

Both `anneal/flake.nix` and `anneal/ci/run_anneal_check.sh` delegate omnibus
staging, exclusion filtering, `libLLVM`/`librustc_driver` symlink deduplication,
and single-pass archive verification to `anneal/ci/pack_omnibus_archive.sh`.
These tests verify that wiring and exercise `pack_omnibus_archive.sh` directly.
"""

# The test methods live in the `run_anneal_check_tests` package, grouped by
# domain into plain mixin classes. Composing them into the test classes
# here lets `unittest` discovery, which loads only `test_*.py` files, find
# each test exactly once under its original class and method names.

from pathlib import Path
import sys
import unittest

_CI_DIR = str(Path(__file__).resolve().parent)
if _CI_DIR not in sys.path:
    sys.path.insert(0, _CI_DIR)
sys.dont_write_bytecode = True

from run_anneal_check_tests.cargo_home_and_extraction import (
    CargoHomeGuardCases,
    PreparedCrateExtractionCases,
)
from run_anneal_check_tests.differential_adapter import DifferentialAdapterParityCases
from run_anneal_check_tests.mode_timeout import ModeTimeoutCases
from run_anneal_check_tests.pack_behavior import PackOmnibusArchiveBehaviorCases
from run_anneal_check_tests.pack_fixture import PackArchiveFixture
from run_anneal_check_tests.pack_wiring import OmnibusPackWiringCases


class OmnibusPackWiringTests(OmnibusPackWiringCases, unittest.TestCase):
    pass


class PackOmnibusArchiveBehaviorTests(
    PackOmnibusArchiveBehaviorCases, PackArchiveFixture, unittest.TestCase
):
    pass


class CargoHomeGuardTests(CargoHomeGuardCases, unittest.TestCase):
    pass


class PreparedCrateExtractionTests(PreparedCrateExtractionCases, unittest.TestCase):
    pass


class ModeTimeoutTests(ModeTimeoutCases, unittest.TestCase):
    pass


class DifferentialAdapterParityTests(DifferentialAdapterParityCases, unittest.TestCase):
    pass


if __name__ == "__main__":
    unittest.main()
