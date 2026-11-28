# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`codex_review` tests for cross-family Gate 2 review results."""

from .gate2_cross_family_binding import Gate2BindingTests
from .gate2_cross_family_coexistence import Gate2CoexistenceTests
from .gate2_cross_family_identity import Gate2IdentityKeyTests
from .gate2_cross_family_antidowngrade import Gate2AntiDowngradeTests
from .gate2_cross_family_tombstones import Gate2TombstoneTests
from .gate2_cross_family_history import Gate2HistoricalFailureChecks
from .support import unittest


class Gate2CrossFamilyTests(
    Gate2BindingTests,
    Gate2CoexistenceTests,
    Gate2IdentityKeyTests,
    Gate2AntiDowngradeTests,
    Gate2TombstoneTests,
    Gate2HistoricalFailureChecks,
    unittest.TestCase,
):
    """Cross-family Gate 2 review tests, assembled from the mixins above."""
