# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Exercise policy boundaries and publication using in-memory GitHub data."""

# The test cases live in the `codex_review_tests` package, one module per
# class. Importing them here lets `unittest` discovery, which loads only
# `test_*.py` files, find each test case exactly once. The shared
# helpers are re-exported for `test_codex_review_properties.py`.

from pathlib import Path
import sys
import unittest

_CI_DIR = str(Path(__file__).resolve().parent)
if _CI_DIR not in sys.path:
    sys.path.insert(0, _CI_DIR)

from codex_review_tests.gate2_carry_forward import Gate2CarryForwardTests
from codex_review_tests.gate2_carry_forward_transport import (
    Gate2CarryForwardTransportTests,
)
from codex_review_tests.gate2_cross_family import Gate2CrossFamilyTests
from codex_review_tests.gate2_delta import Gate2DeltaReviewTests
from codex_review_tests.policy import PolicyTests
from codex_review_tests.reconciliation import ReconciliationTests
from codex_review_tests.transport import TransportTests
from codex_review_tests.support import (
    BASE,
    FakeGitHub,
    gate2_comment,
    gate2_review,
    HEAD,
    OTHER_BASE,
    OTHER_HEAD,
    OTHER_TREE,
    pull,
    summary,
    TREE,
)

__all__ = [
    "BASE",
    "FakeGitHub",
    "gate2_comment",
    "gate2_review",
    "Gate2CarryForwardTests",
    "Gate2CarryForwardTransportTests",
    "Gate2CrossFamilyTests",
    "Gate2DeltaReviewTests",
    "HEAD",
    "OTHER_BASE",
    "OTHER_HEAD",
    "OTHER_TREE",
    "PolicyTests",
    "pull",
    "ReconciliationTests",
    "summary",
    "TransportTests",
    "TREE",
]


if __name__ == "__main__":
    unittest.main()
