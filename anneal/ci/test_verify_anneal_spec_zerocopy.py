# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `ci/verify_anneal_spec_zerocopy.py`."""

# The test methods live in the `verify_anneal_spec_zerocopy_tests` package,
# grouped by domain into plain mixin classes. Composing them into
# `VerifyAnnealSpecZerocopyTests` here lets `unittest` discovery, which loads
# only `test_*.py` files, find each test exactly once under its original
# class and method names.

from pathlib import Path
import sys
import unittest

_CI_DIR = str(Path(__file__).resolve().parent)
if _CI_DIR not in sys.path:
    sys.path.insert(0, _CI_DIR)

from verify_anneal_spec_zerocopy_tests.claim_bound_units import (
    ClaimBoundUnitsCases,
)
from verify_anneal_spec_zerocopy_tests.lean_compile import LeanCompileCases
from verify_anneal_spec_zerocopy_tests.run_suite import RunSuiteCases
from verify_anneal_spec_zerocopy_tests.units_and_sources import (
    UnitsAndSourcesCases,
)


class VerifyAnnealSpecZerocopyTests(
    UnitsAndSourcesCases,
    RunSuiteCases,
    ClaimBoundUnitsCases,
    LeanCompileCases,
    unittest.TestCase,
):
    pass


if __name__ == "__main__":
    unittest.main()
