# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Fast PR gate asserting TrustedBoundary claim sync with Rust audit fixtures."""

# The test methods live in the `trusted_boundary_claim_sync_tests` package,
# grouped by domain into plain mixin classes. Composing them into
# `TrustedBoundaryClaimSyncTests` here lets `unittest` discovery, which loads
# only `test_*.py` files, find each test exactly once under its original
# class and method names.

from pathlib import Path
import sys
import unittest

_CI_DIR = str(Path(__file__).resolve().parent)
if _CI_DIR not in sys.path:
    sys.path.insert(0, _CI_DIR)

from trusted_boundary_claim_sync_tests.claim_parity import ClaimParityCases
from trusted_boundary_claim_sync_tests.fixture_delegation import (
    FixtureDelegationCases,
)
from trusted_boundary_claim_sync_tests.lexer_and_inline_fixtures import (
    LexerAndInlineFixtureCases,
)


class TrustedBoundaryClaimSyncTests(
    ClaimParityCases,
    FixtureDelegationCases,
    LexerAndInlineFixtureCases,
    unittest.TestCase,
):
    pass


if __name__ == "__main__":
    unittest.main()
