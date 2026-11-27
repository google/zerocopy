# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `check_minirust_pin.py`."""

# The test methods live in the `check_minirust_pin_tests` package, grouped
# by domain into plain mixin classes. Composing them into
# `CheckMiniRustPinTests` here lets `unittest` discovery, which loads only
# `test_*.py` files, find each test exactly once under its original class
# and method names.

from pathlib import Path
import sys
import unittest

_CI_DIR = str(Path(__file__).resolve().parent)
if _CI_DIR not in sys.path:
    sys.path.insert(0, _CI_DIR)

from check_minirust_pin_tests.axioms_and_ci import AxiomsAndCiCases
from check_minirust_pin_tests.lean_hygiene import LeanHygieneCases
from check_minirust_pin_tests.spec_anchors import SpecAnchorCases
from check_minirust_pin_tests.vendor_pin import VendorPinCases


class CheckMiniRustPinTests(
    VendorPinCases,
    LeanHygieneCases,
    SpecAnchorCases,
    AxiomsAndCiCases,
    unittest.TestCase,
):
    pass


if __name__ == "__main__":
    unittest.main()
