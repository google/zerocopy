# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `tools/issue_hygiene.py`."""

# The test methods live in the `issue_hygiene_tests` package as mixins, one
# module per test case. Composing them here keeps every test ID
# `test_issue_hygiene.<Class>.<method>`, and lets `unittest` discovery, which
# loads only `test_*.py` files, find each test case exactly once.

from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True

_TOOLS_DIR = str(Path(__file__).resolve().parent)
if _TOOLS_DIR not in sys.path:
    sys.path.insert(0, _TOOLS_DIR)

from issue_hygiene_tests.io_and_cli import IoAndCliCases
from issue_hygiene_tests.tier1 import Tier1Cases
from issue_hygiene_tests.tier2 import Tier2Cases


class IssueHygieneTier1Tests(Tier1Cases, unittest.TestCase):
    pass


class IssueHygieneTier2Tests(Tier2Cases, unittest.TestCase):
    pass


class IssueHygieneIoAndCliTests(IoAndCliCases, unittest.TestCase):
    pass


if __name__ == "__main__":
    unittest.main()
