# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit and fault-injection tests for `anneal/ci/alpha_release.py`."""

# The test methods live in the `alpha_release_tests` package, grouped by
# domain into plain mixin classes. Composing them into `AlphaReleaseTests`
# here lets `unittest` discovery, which loads only `test_*.py` files, find
# each test exactly once under its original class and method names.

from pathlib import Path
import sys
import unittest

_CI_DIR = str(Path(__file__).resolve().parent)
if _CI_DIR not in sys.path:
    sys.path.insert(0, _CI_DIR)

from alpha_release_tests.crate_verifier import CrateVerifierCases
from alpha_release_tests.manifest_and_stamp import ManifestAndStampCases
from alpha_release_tests.published_crate import PublishedCrateCases
from alpha_release_tests.resolve_and_recovery import ResolveAndRecoveryCases


class AlphaReleaseTests(
    ManifestAndStampCases,
    CrateVerifierCases,
    ResolveAndRecoveryCases,
    PublishedCrateCases,
    unittest.TestCase,
):
    pass


if __name__ == "__main__":
    unittest.main()
